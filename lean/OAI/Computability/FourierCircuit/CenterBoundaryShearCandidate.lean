import OAI.Computability.FourierCircuit.CenterBoundaryObstruction
import OAI.Computability.FourierCircuit.CenterFrameDirectionAudit
import Mathlib.Tactic

/-!
# A reversible shear candidate for the centre boundary

`CenterBoundaryObstruction` shows that the raw target line `P ⊗ t` is absent
from the target boundary `B ⊗ D + P ⊗ t^⊥`.  This file records the smallest
local repair we found: apply the binary isotropic transvection
`unitCoordinateEquiv t w` to the active factor, where `t w = 0`.  It sends
`t` to the coordinate line `e_w`, and that line lies in `t^⊥`.  Thus the
sheared direct line is legal at the old target boundary.

This is a local label certificate only.  It does not assert that the shear can
be scheduled for every centre bank without an additional gate/frame charge.
The latter charge is recorded in the independent arithmetic definitions below.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryShearCandidate

open CenterBoundaryObstruction
open CenterFrameDirectionAudit
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- The coordinate image of a unit target line is in the old target boundary. -/
theorem unit_line_sheared_into_targetPerp
    {h : ℕ} (t : Active h) (w : Fin h)
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    unitCoordinateEquiv t w ht hw t ∈ targetPerp t := by
  change unitCoordinateEquiv t w ht hw t ∈
    (F ∙ t).orthogonalBilin (BinaryTransvection.bilinearDot : _)
  rw [Submodule.orthogonalBilin_span_singleton]
  change dotProduct t (unitCoordinateEquiv t w ht hw t) = 0
  rw [unitCoordinateEquiv_unit t w ht hw]
  rw [dot_coordinate]
  exact hw

/-- After the shear, the inserted target line is carried by the old L5 frame. -/
theorem sheared_insert_mem_L5
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (w : Fin h) (hw : t w = 0) :
    SideRowGeneralArbitrary.insertP p
        (unitCoordinateEquiv t w ht hw t) ∈
      SideRowGeneralArbitrary.L5 p t := by
  rw [Submodule.mem_comap]
  rw [SideRowGeneralArbitrary.project_insertP p hp]
  exact (unit_line_sheared_into_targetPerp t w ht hw)

/-- The shear is reversible: applying it twice returns the original line. -/
theorem sheared_line_involutive
    {h : ℕ} (t : Active h) (w : Fin h)
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    unitCoordinateEquiv t w ht hw
      (unitCoordinateEquiv t w ht hw t) = t := by
  exact (unitCoordinateEquiv t w ht hw).left_inv t

/- If one changes the target frame by explicitly adding the raw target line,
   the active target frame becomes the whole space.  This is the exact
   codimension-one price of the naive boundary redesign. -/
theorem targetPerp_sup_target_line_eq_top
    {h : ℕ} (t : Active h)
    (ht : dotProduct t t = (1 : F)) :
    targetPerp t ⊔ (F ∙ t) = ⊤ := by
  have hnonzero :
      (BinaryTransvection.bilinearDot t) t ≠ (0 : F) := by
    change dotProduct t t ≠ (0 : F)
    rw [ht]
    exact one_ne_zero
  exact (LinearMap.isCompl_span_singleton_orthogonal hnonzero).symm.sup_eq_top

theorem full_target_frame_eq_top
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (ht : dotProduct t t = (1 : F)) :
    (targetPerp t ⊔ (F ∙ t)).comap
        (SideRowGeneralArbitrary.projectP p) = ⊤ := by
  rw [targetPerp_sup_target_line_eq_top t ht]
  exact Submodule.comap_top _

/-- h=24 instance using the concrete target vector from the frame audit. -/
theorem h24_sheared_target_boundary :
    SideRowGeneralArbitrary.insertP
        (StagePrefixAudit.prefixUnit (ι := Fin 1) 0)
        (unitCoordinateEquiv targetVec w targetVec_unit targetVec_zero_at_w targetVec) ∈
      SideRowGeneralArbitrary.L5
        (StagePrefixAudit.prefixUnit (ι := Fin 1) 0) targetVec := by
  exact sheared_insert_mem_L5
    (StagePrefixAudit.prefixUnit (ι := Fin 1) 0) targetVec
    (StagePrefixAudit.prefixUnit_unit (ι := Fin 1) 0)
    targetVec_unit w targetVec_zero_at_w

namespace H24

/- The direct line can be repaired with one active-factor transvection.  The
   arithmetic below treats one such transvection as one directional unit per
   centre role; this is a proposed price, not a theorem about the global DAG. -/
def h : ℕ := 24
def v : ℕ := CenterCompression.H24.v
def I : ℕ := CenterCompression.H24.I0

def centreFusionSaving : ℤ :=
  2 * (CenterCompression.H24.N0 : ℤ) - 4 * (v : ℤ)^2 * (h : ℤ)^2

def oneShearCharge : ℤ := (I : ℤ) * (h : ℤ)
def shearedFusionMargin : ℤ := centreFusionSaving - oneShearCharge

def m : ℕ := CenterCompression.H24.m
def Wstar : ℕ := CenterCompression.H24.Wstar
def shearedNormalized : ℚ :=
  (shearedFusionMargin : ℚ) / ((m : ℚ) * (Wstar : ℚ))

theorem centreFusionSaving_eq : centreFusionSaving = 7144428544 := by
  norm_num [centreFusionSaving, v, h, CenterCompression.H24.N0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem oneShearCharge_eq : oneShearCharge = 294953472 := by
  norm_num [oneShearCharge, I, h, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem shearedFusionMargin_eq : shearedFusionMargin = 6849475072 := by
  norm_num [shearedFusionMargin, centreFusionSaving_eq, oneShearCharge_eq]

theorem shearedFusionMargin_pos : 0 < shearedFusionMargin := by
  rw [shearedFusionMargin_eq]
  norm_num

theorem shearedNormalized_eq :
    shearedNormalized = 13377881 / 949978046398464 := by
  norm_num [shearedNormalized, shearedFusionMargin_eq, m, Wstar,
    CenterCompression.H24.m, CenterCompression.H24.Wstar,
    CenterCompression.H24.h]

theorem shearedNormalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < shearedNormalized := by
  rw [shearedNormalized_eq]
  norm_num

end H24

end CenterBoundaryShearCandidate
end ExactFourier
end OAI
