import OAI.Computability.FourierCircuit.CenterBoundaryFusedReadout
import OAI.Computability.FourierCircuit.BinaryTransvection
import Mathlib.Tactic

/-!
# A selective full-address transvection for the centre boundary

The old target boundary misses the direct line `p ⊗ t`, although it contains
`p ⊗ e_w` whenever `t w = 0`.  This file records a purely local algebraic
repair.  Put `d = p ⊗ t`, `e = p ⊗ e_w`, and `s = d + e`.  Under the source
orthogonality assumptions, `s` is isotropic and orthogonal to the whole old
source row `L2 p x`.  The full-address transvection by `s` therefore fixes the
source contribution and sends `d` to `e`.

This is deliberately only an algebraic commuting-square certificate.  It does
not identify this transvection with a single common-frame gate in the paper's
tensor schedule, nor does it prove a directional-operation cost.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundarySelectiveTransvection

open CenterRowGeneral
open CenterBoundaryObstruction
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}

/-- The direct and legal coordinate contributions at a fixed prefix. -/
abbrev d (p : ι → F) (t : Active h) : Address ι h := insert p t

abbrev e (p : ι → F) (w : Fin h) : Address ι h :=
  insert p (coordinate w)

/-- The isotropic direction used by the selective transvection. -/
abbrev axis (p : ι → F) (t : Active h) (w : Fin h) : Address ι h :=
  d p t + e p w

theorem axis_eq_insert (p : ι → F) (t : Active h) (w : Fin h) :
    axis p t w = insert p (t + coordinate w) := by
  change insert p t + insert p (coordinate w) = insert p (t + coordinate w)
  rw [← (insert p).map_add]

noncomputable abbrev W (p : ι → F) (t : Active h) (w : Fin h) :
    Address ι h →ₗ[F] Address ι h :=
  transvection (axis p t w)

theorem d_dot_d (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) :
    dotProduct (d p t) (d p t) = (1 : F) := by
  exact insert_dot_insert p hp t t |>.trans ht

theorem e_dot_e (p : ι → F) (w : Fin h)
    (hp : dotProduct p p = (1 : F)) :
    dotProduct (e p w) (e p w) = (1 : F) := by
  rw [e, insert_dot_insert p hp, coordinate_dot]
  simp [coordinate]

theorem d_dot_e (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F)) :
    dotProduct (d p t) (e p w) = t w := by
  rw [d, e, insert_dot_insert p hp, dot_coordinate]

theorem axis_isotropic (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    dotProduct (axis p t w) (axis p t w) = (0 : F) := by
  rw [axis_eq_insert, insert_dot_insert p hp]
  exact unit_shift_isotropic t w ht hw

theorem axis_dot_d (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    dotProduct (axis p t w) (d p t) = (1 : F) := by
  rw [axis_eq_insert, insert_dot_insert p hp]
  simp [add_dotProduct, coordinate_dot, ht, hw]

theorem axis_dot_active (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) :
    dotProduct (axis p t w) (insert p x) = (0 : F) := by
  have htx : dotProduct t x = 0 := by
    rw [dotProduct_comm]
    exact hxt
  rw [axis_eq_insert, insert_dot_insert p hp]
  simp [add_dotProduct, coordinate_dot, htx, hxw]

theorem axis_dot_L2 (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0)
    (z : Address ι h) (hz : z ∈ L2 p x) :
    dotProduct (axis p t w) z = (0 : F) := by
  rw [axis_eq_insert]
  rw [insert_dot]
  have hz' : project p z ∈ line x := hz
  rcases Submodule.mem_span_singleton.mp hz' with ⟨a, ha⟩
  rw [← ha, dotProduct_smul]
  have htx : dotProduct t x = 0 := by
    rw [dotProduct_comm]
    exact hxt
  have hactive : dotProduct (t + coordinate w) x = 0 := by
    rw [add_dotProduct]
    simp [htx, coordinate_dot, hxw]
  rw [hactive]
  simp

theorem W_isometry (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0)
    (z z' : Address ι h) :
    dotProduct (W p t w z) (W p t w z') = dotProduct z z' := by
  exact transvection_dot _ _ _ (axis_isotropic p t w hp ht hw)

theorem W_involutive (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    Function.Involutive (W p t w) := by
  exact transvection_involutive _ (axis_isotropic p t w hp ht hw)

theorem W_fix_L2 (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0)
    (z : Address ι h) (hz : z ∈ L2 p x) :
    W p t w z = z := by
  rw [W, transvection_apply, axis_dot_L2 p x t w hp hxt hxw z hz]
  simp

theorem W_map_d_to_e (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    W p t w (d p t) = e p w := by
  rw [W, transvection_apply, axis_dot_d p t w hp ht hw]
  simp only [one_smul]
  rw [axis_eq_insert]
  change insert p t + insert p (t + coordinate w) = insert p (coordinate w)
  rw [← (insert p).map_add]
  congr 1
  ext j
  simp only [Pi.add_apply]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem W_map_source_plus_d (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (z : Address ι h) (hz : z ∈ L2 p x) :
    W p t w (z + d p t) = z + e p w := by
  rw [map_add, W_fix_L2 p x t w hp hxt hxw z hz,
    W_map_d_to_e p t w hp ht hw]

theorem e_mem_L5 (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F)) (hw : t w = 0) :
    e p w ∈ L5 p t := by
  rw [Submodule.mem_comap, project_insertP p hp]
  change coordinate w ∈ (F ∙ t).orthogonalBilin
      (BinaryTransvection.bilinearDot : _)
  rw [Submodule.orthogonalBilin_span_singleton]
  change dotProduct t (coordinate w) = 0
  rw [dot_coordinate, hw]

theorem d_not_mem_L5 (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) :
    d p t ∉ L5 p t := by
  intro hd
  rw [Submodule.mem_comap, project_insertP p hp] at hd
  exact target_line_not_targetPerp t ht hd

theorem W_does_not_preserve_L5 (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    ¬ ∀ z ∈ L5 p t, W p t w z ∈ L5 p t := by
  intro hpres
  have he : e p w ∈ L5 p t := e_mem_L5 p t w hp hw
  have hback : W p t w (e p w) = d p t := by
    have hinv := W_involutive p t w hp ht hw (d p t)
    rw [W_map_d_to_e p t w hp ht hw] at hinv
    exact hinv
  apply d_not_mem_L5 p t hp ht
  rw [← hback]
  exact hpres (e p w) he

theorem W_map_source_plus_d_mem_L5 (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (z : Address ι h) (hz : z ∈ L2 p x) :
    W p t w (z + d p t) ∈ L5 p t := by
  rw [W_map_source_plus_d p x t w hp ht hxt hw hxw z hz]
  have hzL5 : z ∈ L5 p t := L2_le_L5 p x t hxt hz
  exact (L5 p t).add_mem hzL5 (e_mem_L5 p t w hp hw)

end CenterBoundarySelectiveTransvection
end ExactFourier
end OAI
