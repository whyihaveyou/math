import OAI.Computability.FourierCircuit.ArbitraryTwoFrameCover
import OAI.Computability.FourierCircuit.DenseBlockBoundaryArithmetic
import Mathlib.Tactic

/-!
# Unique target frame and exact two-block switch count

`ArbitraryTwoFrameCover` proves that the dense labels
`u = e₀` and `w = 1 + e₀` have exactly one member in every target boundary
when `h` is even.  This file turns that local fact into a finite block-order
ledger.  The order `[u, w]` has one frame change; the three prefix sizes
`1, h, h^2` therefore charge `2 * (1 + h + h^2)` directional units.

The schedule is deliberately a serialized block-order premise.  No theorem
here forms the target aggregates, implements the complex gate, proves that the
blocks can be buffered by the paper network, or supplies the all-length DFT
recurrence.
-/

namespace OAI
namespace ExactFourier
namespace DenseBlockFrameSwitch

open ArbitraryTwoFrameCover
open CenterCompression
open FrameLabels
open ParityTargetAggregateFrameCandidate

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Triple (h : ℕ) := CenterCompression.Triple h

inductive TargetFrame
  | unit
  | dense
  deriving DecidableEq, Repr

def frameLabel {h : ℕ} (hh : 4 ≤ h) (S : Triple h) : Active h :=
  if zeroIndex (by omega : 1 ≤ h) ∈ S.1 then
    denseComplementLabel (by omega)
  else
    unitLabel (by omega)

def frameValue {h : ℕ} (hh : 4 ≤ h) : TargetFrame → Active h
  | .unit => unitLabel (by omega)
  | .dense => denseComplementLabel (by omega)

def frameOfTarget {h : ℕ} (hh : 4 ≤ h) (S : Triple h) : TargetFrame :=
  if zeroIndex (by omega : 1 ≤ h) ∈ S.1 then .dense else .unit

theorem frameOfTarget_label_eq {h : ℕ} (hh : 4 ≤ h) (S : Triple h) :
    frameValue hh (frameOfTarget hh S) = frameLabel hh S := by
  by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1 <;>
    simp [frameOfTarget, frameLabel, frameValue, hz]

theorem frameOfTarget_mem_boundary {h : ℕ} (hh : 4 ≤ h)
    (heven : Even h) (S : Triple h) :
    frameValue hh (frameOfTarget hh S) ∈
      targetBoundary S := by
  by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1
  · rw [frameOfTarget, if_pos hz]
    change denseComplementLabel (by omega) ∈ targetBoundary S
    rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
    change dotForm (indicator S.1)
      (denseComplementLabel (by omega)) = 0
    exact target_dot_dense_of_mem (by omega) S hz
  · rw [frameOfTarget, if_neg hz]
    change unitLabel (by omega) ∈ targetBoundary S
    rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
    change dotForm (indicator S.1) (unitLabel (by omega)) = 0
    rw [target_dot_unit, if_neg hz]

theorem frameOfTarget_unique {h : ℕ} (hh : 4 ≤ h)
    (heven : Even h) (S : Triple h) :
    ∀ f : TargetFrame,
      frameValue hh f ∈ targetBoundary S ↔ f = frameOfTarget hh S := by
  intro f
  cases f with
  | unit =>
      by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1
      · rw [frameOfTarget, if_pos hz]
        constructor
        · intro hu
          exfalso
          rw [targetBoundary, Submodule.orthogonalBilin_span_singleton] at hu
          change dotForm (indicator S.1) (unitLabel (by omega)) = 0 at hu
          rw [target_dot_unit, if_pos hz] at hu
          exact one_ne_zero hu
        · intro hEq
          cases hEq
      · rw [frameOfTarget, if_neg hz]
        constructor
        · intro hu
          rfl
        · intro _
          simpa [frameOfTarget, hz] using frameOfTarget_mem_boundary hh heven S
  | dense =>
      by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1
      · rw [frameOfTarget, if_pos hz]
        constructor
        · intro hw
          rfl
        · intro _
          simpa [frameOfTarget, hz] using frameOfTarget_mem_boundary hh heven S
      · rw [frameOfTarget, if_neg hz]
        constructor
        · intro hw
          exfalso
          rw [targetBoundary, Submodule.orthogonalBilin_span_singleton] at hw
          change dotForm (indicator S.1)
            (denseComplementLabel (by omega)) = 0 at hw
          rw [target_dot_dense_of_not_mem (by omega) S hz] at hw
          exact one_ne_zero hw
        · intro hEq
          cases hEq

/-! ## A finite block order and its exact switch count -/

def blockOrder : List TargetFrame := [.unit, .dense]

def switchCount : List TargetFrame → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => (if x = y then 0 else 1) + switchCount (y :: xs)

theorem blockOrder_switchCount : switchCount blockOrder = 1 := by
  norm_num [blockOrder, switchCount]

def prefixSizes (h : ℕ) : List ℕ := [1, h, h ^ 2]

def weightedSwitchCharge (h : ℕ) : ℕ :=
  2 * switchCount blockOrder * (prefixSizes h).sum

theorem prefixSizes_h24_sum : (prefixSizes 24).sum = 601 := by
  norm_num [prefixSizes]

theorem weightedSwitchCharge_h24 : weightedSwitchCharge 24 = 1202 := by
  norm_num [weightedSwitchCharge, blockOrder_switchCount, prefixSizes]

/-! ## Link to the existing exact normalized ledger -/

abbrev conditionalMargin : ℤ :=
  (DenseBlockBoundaryArithmetic.H24.saving : ℤ) -
    (weightedSwitchCharge 24 : ℤ)

abbrev conditionalNormalized : ℚ :=
  conditionalMargin /
    ((DenseBlockBoundaryArithmetic.H24.m : ℚ) *
      (CenterCompression.H24.Wstar : ℚ))

theorem conditionalMargin_eq : conditionalMargin = 2425171790 := by
  rw [conditionalMargin, DenseBlockBoundaryArithmetic.H24.saving_eq,
    weightedSwitchCharge_h24]
  norm_num

theorem conditionalNormalized_eq :
    conditionalNormalized = 1212585895 / 243194379878006784 := by
  rw [conditionalNormalized, conditionalMargin_eq,
    DenseBlockBoundaryArithmetic.H24.m_eq,
    CenterCompression.H24.Wstar_eq]
  norm_num

theorem conditionalNormalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < conditionalNormalized := by
  rw [conditionalNormalized_eq]
  norm_num

end DenseBlockFrameSwitch
end ExactFourier
end OAI
