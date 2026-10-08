import OAI.Computability.FourierCircuit.DenseTwoFrameComplexBridge
import OAI.Computability.FourierCircuit.DenseBlockFrameSwitch
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Target-routed dense frames: exact local bridge and its phase obstruction

The two-label dense cover has an exact target-indexed route: the identity on
the unit block and `denseSwap` on the dense block.  This file proves that the
route maps the anchored unit label to the unique boundary label and that its
address lift is monomial.  Under the explicit premise that this target-indexed
address relabelling is free, the switch charge is zero, improving the finite
H24 ledger by exactly 1,202 units.

The second half records the remaining obstruction.  `denseSwap` is not a
universal phase symmetry: there is a complex diagonal profile that it
relabels nontrivially.  Hence zero switch cost still requires a concrete phase
transport (or an invariance proof) for the supplied `q_U` profile.  Neither
part is an unconditional complex-circuit or all-length DFT theorem.
-/

namespace OAI
namespace ExactFourier
namespace DenseTargetRoutedFrameAudit

open ArbitraryTwoFrameCover
open DenseBlockFrameSwitch
open DenseTwoFrameComplexBridge
open CenterBoundaryTensorLift
open BinaryAddressPermutation
open AddressPhaseConjugation
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Triple (h : ℕ) := CenterCompression.Triple h
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

/-! ## Exact target-indexed route -/

noncomputable def targetRoute {h : ℕ} (hh : 4 ≤ h) (heven : Even h)
    (S : Triple h) : Active h ≃ₗ[F] Active h :=
  match frameOfTarget hh S with
  | .unit => LinearEquiv.refl F (Active h)
  | .dense => denseSwap h (by omega) heven

theorem targetRoute_unitLabel {h : ℕ} (hh : 4 ≤ h) (heven : Even h)
    (S : Triple h) :
    targetRoute hh heven S (unitLabel (by omega : 1 ≤ h)) =
      frameValue hh (frameOfTarget hh S) := by
  by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1
  · simp [targetRoute, frameOfTarget, frameValue, hz, unitLabel]
    exact denseSwap_coordinate (by omega) heven
  · simp [targetRoute, frameOfTarget, frameValue, hz, unitLabel]

theorem targetRoute_address_monomial
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 4 ≤ h) (heven : Even h) (S : Triple h) :
    MonomialMatrix
      (BinaryAddressPermutation.matrix (ι := ι × Fin h)
        (lift (ι := ι) (targetRoute hh heven S))) := by
  exact BinaryAddressPermutation.matrix_monomial
    (lift (ι := ι) (targetRoute hh heven S))

/-! ## The conditional zero-switch ledger -/

def targetIndexedSwitchCharge : ℕ := 0

theorem targetIndexedSwitchCharge_eq : targetIndexedSwitchCharge = 0 := by
  rfl

namespace H24

abbrev saving : ℕ := CenterCompression.H24.deltaCompressed
abbrev m : ℕ := CenterCompression.H24.m
abbrev Wstar : ℕ := CenterCompression.H24.Wstar

def zeroSwitchMargin : ℤ := (saving : ℤ) - targetIndexedSwitchCharge
def zeroSwitchNormalized : ℚ :=
  zeroSwitchMargin / ((m : ℚ) * (Wstar : ℚ))

theorem zeroSwitchMargin_eq : zeroSwitchMargin = 2425172992 := by
  rw [zeroSwitchMargin, targetIndexedSwitchCharge_eq]
  norm_num [saving, CenterCompression.H24.deltaCompressed_eq]

theorem zeroSwitchNormalized_eq :
    zeroSwitchNormalized = 2368333 / 474989023199232 := by
  rw [zeroSwitchNormalized, zeroSwitchMargin_eq]
  norm_num [m, Wstar, CenterCompression.H24.m,
    CenterCompression.H24.Wstar, CenterCompression.H24.h]

theorem zeroSwitchNormalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < zeroSwitchNormalized := by
  rw [zeroSwitchNormalized_eq]
  norm_num

theorem zeroSwitchNormalized_gt_dense_block_switch :
    DenseBlockFrameSwitch.conditionalNormalized < zeroSwitchNormalized := by
  rw [zeroSwitchNormalized_eq,
    DenseBlockFrameSwitch.conditionalNormalized_eq]
  norm_num

/-! The finite `ε` and the inherited recurrence exponent are different
quantities.  The following interface makes the distinction explicit and
checks that this route cannot reach a `10⁻⁹` exponent gap. -/

noncomputable def zeroSwitchEpsilon : ℝ :=
  (zeroSwitchNormalized : ℚ)

noncomputable def zeroSwitchExponentGap : ℝ :=
  -Real.log (1 - zeroSwitchEpsilon) / Real.log (13824 : ℝ)

theorem zeroSwitchEpsilon_pos : 0 < zeroSwitchEpsilon := by
  rw [zeroSwitchEpsilon, zeroSwitchNormalized_eq]
  norm_num

theorem zeroSwitchEpsilon_lt_five_nano :
    zeroSwitchEpsilon < (5 : ℝ) / 10 ^ 9 := by
  rw [zeroSwitchEpsilon, zeroSwitchNormalized_eq]
  norm_num

private lemma neg_log_one_sub_le_div {e : ℝ} (hepos : 0 < e)
    (helt : e < 1) :
    -Real.log (1 - e) ≤ e / (1 - e) := by
  have hpos : 0 < 1 - e := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  calc
    -Real.log (1 - e) = Real.log ((1 - e)⁻¹) := by
      rw [Real.log_inv]
    _ ≤ (1 - e)⁻¹ - 1 := hlog
    _ = e / (1 - e) := by field_simp; ring

private lemma log_h24_gt_nine :
    (9 : ℝ) < Real.log (13824 : ℝ) := by
  have hexp : Real.exp (9 : ℝ) < (13824 : ℝ) := by
    rw [show (9 : ℝ) = (9 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have hp : (Real.exp 1) ^ (9 : ℕ) <
        (2.7182818286 : ℝ) ^ (9 : ℕ) := by
      exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
    have hnum : (2.7182818286 : ℝ) ^ (9 : ℕ) < (13824 : ℝ) := by
      norm_num
    exact hp.trans hnum
  exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hexp

theorem zeroSwitchExponentGap_lt_one_e_minus_nine :
    zeroSwitchExponentGap < (1 : ℝ) / 10 ^ 9 := by
  have hepos := zeroSwitchEpsilon_pos
  have he5 := zeroSwitchEpsilon_lt_five_nano
  have helt : zeroSwitchEpsilon < 1 := by nlinarith [he5]
  have hone : 0 < 1 - zeroSwitchEpsilon := by linarith
  have hnum_le := neg_log_one_sub_le_div hepos helt
  have hnum_lt :
      -Real.log (1 - zeroSwitchEpsilon) < (6 : ℝ) / 10 ^ 9 := by
    have hfrac : zeroSwitchEpsilon / (1 - zeroSwitchEpsilon) <
        (6 : ℝ) / 10 ^ 9 := by
      apply (div_lt_iff₀ hone).2
      nlinarith [he5]
    exact hnum_le.trans_lt hfrac
  have hlogpos : 0 < Real.log (13824 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog9 := log_h24_gt_nine
  rw [zeroSwitchExponentGap]
  apply (div_lt_iff₀ hlogpos).2
  have htarget : (6 : ℝ) / 10 ^ 9 <
      (1 : ℝ) / 10 ^ 9 * Real.log (13824 : ℝ) := by
    nlinarith [hlog9]
  exact hnum_lt.trans htarget

end H24

/-! ## A phase-profile no-go for dropping the address relabelling -/

noncomputable def anchorAddress {h : ℕ} (hh : 1 ≤ h) : Address PUnit h :=
  fun q => coordinate (zeroIndex hh) q.2

theorem denseSwap_lift_anchor_ne
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    (lift (ι := PUnit) (denseSwap h hh heven)) (anchorAddress (h := h) (by omega)) ≠
      anchorAddress (h := h) (by omega) := by
  intro hEq
  have hcoord := congrFun hEq
    (PUnit.unit, zeroIndex (by omega : 1 ≤ h))
  rw [lift_apply] at hcoord
  have hcoord' :
      denseSwap h hh heven
          (coordinate (zeroIndex (by omega : 1 ≤ h)))
          (zeroIndex (by omega : 1 ≤ h)) =
        coordinate (zeroIndex (by omega : 1 ≤ h))
          (zeroIndex (by omega : 1 ≤ h)) := by
    simpa [anchorAddress] using hcoord
  rw [denseSwap_coordinate (by omega) heven] at hcoord'
  rw [denseComplement_zero (h := h) (by omega : 1 ≤ h)] at hcoord'
  norm_num [coordinate, zeroIndex] at hcoord'

theorem denseSwap_not_universal_phase_invariant
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    ¬ (∀ q : Address PUnit h → ℂ,
      q ∘ (fun x =>
        (BinaryAddressPermutation.induced
          (lift (ι := PUnit) (denseSwap h hh heven))).symm x) = q) := by
  intro hall
  let e : Address PUnit h ≃ₗ[F] Address PUnit h :=
    lift (ι := PUnit) (denseSwap h hh heven)
  let a : Address PUnit h := anchorAddress (h := h) (by omega)
  let q : Address PUnit h → ℂ := fun x => if x = a then 1 else 0
  have hne : e a ≠ a := by
    exact denseSwap_lift_anchor_ne hh heven
  have hq := hall q
  have hq' := congrFun hq (BinaryAddressPermutation.induced e a)
  change q (e.symm (e a)) = q (e a) at hq'
  rw [e.symm_apply_apply] at hq'
  simp [q, hne] at hq'

end DenseTargetRoutedFrameAudit
end ExactFourier
end OAI
