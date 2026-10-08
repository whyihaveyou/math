import OAI.Computability.FourierCircuit.CenterBoundarySelectiveTransvection
import Mathlib.Tactic

/-!
# Noninterference of selective centre transports on orthogonal prefix banks

The selective transvection has axis `p ⊗ (t + e_w)`.  If another bank has
prefix `q` with `p · q = 0`, every vector inserted along `q` is fixed.  Two
selective transports on orthogonal prefix banks also commute.  These are
actual algebraic noninterference laws and need no hypothesis on the two
active labels.  They apply only when the prefix orthogonality is proved;
they do not supply a global partition of all centre roles, a complex gate
implementation, or its cost.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryOrthogonalBankTransport

open CenterRowGeneral
open CenterBoundarySelectiveTransvection
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}

omit [DecidableEq ι] in
/-- Contracting a tensor inserted along a different prefix exposes their
    prefix dot product. -/
theorem project_insert_cross (p q : ι → F) (a : Active h) :
    project p (insert q a) = dotProduct p q • a := by
  ext j
  change dotProduct p (fun i => q i * a j) = (dotProduct p q • a) j
  have hfun : (fun i => q i * a j) = (a j) • q := by
    ext i
    exact mul_comm _ _
  rw [hfun, dotProduct_smul]
  simp [smul_eq_mul, mul_comm]

omit [DecidableEq ι] in
theorem insert_cross_dot (p q : ι → F) (a b : Active h) :
    dotProduct (insert p a) (insert q b) =
      dotProduct p q * dotProduct a b := by
  rw [insert_dot, project_insert_cross, dotProduct_smul]
  rfl

/-- A selective repair fixes every vector on a different orthogonal prefix
    bank, even when the active vectors overlap. -/
theorem W_fix_orthogonal_insert (p q : ι → F) (t a : Active h) (w : Fin h)
    (hpq : dotProduct p q = 0) :
    W p t w (insert q a) = insert q a := by
  rw [W, transvection_apply, axis_eq_insert, insert_cross_dot, hpq]
  simp

theorem W_fix_orthogonal_residual (p q : ι → F) (t : Active h) (w : Fin h)
    (hpq : dotProduct p q = 0)
    (z : Address ι h) (hz : z ∈ residual q) :
    W p t w z = z := by
  rcases hz with ⟨a, rfl⟩
  exact W_fix_orthogonal_insert p q t a w hpq

/-- Orthogonal axes give commuting transvections.  Isotropy is needed for
    each transvection to be an isometry but is not needed for this identity. -/
theorem transvection_commute_of_orthogonal
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u v z : κ → F) (huv : dotProduct u v = 0) :
    transvection u (transvection v z) =
      transvection v (transvection u z) := by
  have hvu : dotProduct v u = 0 := by
    rw [dotProduct_comm]
    exact huv
  simp only [transvection_apply, dotProduct_add, dotProduct_smul,
    huv, hvu, smul_zero, add_zero]
  abel

/-- The concrete selective transports commute whenever their prefix banks
    are orthogonal. -/
theorem W_commute_of_orthogonal_prefix
    (p q : ι → F) (t s : Active h) (w v : Fin h)
    (hpq : dotProduct p q = 0) (z : Address ι h) :
    W p t w (W q s v z) = W q s v (W p t w z) := by
  apply transvection_commute_of_orthogonal
  rw [axis_eq_insert, axis_eq_insert, insert_cross_dot, hpq, zero_mul]

/-- A sharper criterion for a shared prefix: the two full-address axes, not
    merely the prefixes, must be orthogonal. -/
theorem W_commute_of_axis_orthogonal
    (p : ι → F) (t s : Active h) (w v : Fin h)
    (haxis : dotProduct (t + coordinate w) (s + coordinate v) = 0)
    (z : Address ι h) :
    W p t w (W p s v z) = W p s v (W p t w z) := by
  apply transvection_commute_of_orthogonal
  rw [axis_eq_insert, axis_eq_insert, insert_cross_dot]
  simp [haxis]

/-- For an arbitrary pair of prefixes, the exact obstruction term factors
    into a prefix dot product and an active-axis dot product. -/
theorem axis_cross_dot
    (p q : ι → F) (t s : Active h) (w v : Fin h) :
    dotProduct (axis p t w) (axis q s v) =
      dotProduct p q * dotProduct (t + coordinate w) (s + coordinate v) := by
  rw [axis_eq_insert, axis_eq_insert, insert_cross_dot]

/-- A shared zero coordinate is not enough to make repairs commute.  On one
    unit prefix, repairs of two orthogonal unit labels using the same witness
    disagree already on the inserted first target. -/
theorem shared_witness_repairs_disagree
    (p : ι → F) (t s : Active h) (w : Fin h)
    (hp : dotProduct p p = 1)
    (ht : dotProduct t t = 1) (hs : dotProduct s s = 1)
    (hts : dotProduct t s = 0) (htw : t w = 0) (hsw : s w = 0) :
    W p t w (W p s w (d p t)) ≠ W p s w (W p t w (d p t)) := by
  have hfix : W p s w (d p t) = d p t := by
    rw [W, transvection_apply, axis_dot_active p t s w hp hts htw]
    simp
  have hback : W p s w (e p w) = d p s := by
    have hi := W_involutive p s w hp hs hsw (d p s)
    rw [W_map_d_to_e p s w hp hs hsw] at hi
    exact hi
  rw [hfix, W_map_d_to_e p t w hp ht htw, hback]
  intro heq
  have hproject := congrArg (project p) heq
  change project p (insert p (coordinate w)) = project p (insert p s) at hproject
  rw [project_insert p hp, project_insert p hp] at hproject
  have hval := congrFun hproject w
  simp [coordinate, hsw] at hval

theorem shared_witness_repairs_not_commuting
    (p : ι → F) (t s : Active h) (w : Fin h)
    (hp : dotProduct p p = 1)
    (ht : dotProduct t t = 1) (hs : dotProduct s s = 1)
    (hts : dotProduct t s = 0) (htw : t w = 0) (hsw : s w = 0) :
    ¬ ∀ z, W p t w (W p s w z) = W p s w (W p t w z) := by
  intro hcommute
  exact shared_witness_repairs_disagree p t s w hp ht hs hts htw hsw
    (hcommute (d p t))

end CenterBoundaryOrthogonalBankTransport
end ExactFourier
end OAI
