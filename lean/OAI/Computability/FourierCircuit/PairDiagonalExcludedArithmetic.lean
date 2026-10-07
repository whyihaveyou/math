import OAI.Computability.FourierCircuit.PairHierarchyNearMiss
import Mathlib.Tactic.NormNum

/-!
# Diagonal-excluded pair-prefix arithmetic candidate

For a target triple S and a pair F ⊂ S, the pair aggregate
`a_F = sum_{T ⊃ F} x_T` contains the unwanted diagonal term `x_S`.
Removing that term leaves the h-3 indicators `t_T` with T ⊃ F and T ≠ S.
A separate finite-field audit records that these vectors have rank h-3 and
are contained in `t_S^perp` at h=24.  This file only records the arithmetic
that would follow from a deliberately optimistic schedule: one codimension-2
transition per pair aggregate across stages 2 and 3.  It does not assert that
such a cross-stage schedule exists, nor that source accumulation and target
readout have been implemented.
-/

namespace OAI
namespace ExactFourier
namespace PairDiagonalExcludedArithmetic
namespace H24

open CenterCompression
open PairHierarchyNearMiss.H24
open SideHierarchyArithmetic.H24

/-- Number of pair aggregates in one invocation. -/
def pairAggregateCount : ℕ := pairCount

/-- Naive scalar role count after replacing ordered side roles by pair moments. -/
def roleCount : ℕ := pairRoleCount

/-- The next power-of-two padding for that role count. -/
def padding : ℕ := pairPadding

/-- Two stages, one codimension-two transition per pair aggregate. -/
def optimisticPenalty : ℕ := oneWayCodimTwoPenalty

/-- Centre saving after the optimistic boundary charge. -/
def effectiveSaving : ℕ :=
  CenterCompression.H24.deltaCompressed - optimisticPenalty

/-- Normalized saving under the pair padding. -/
def normalizedSaving : ℚ :=
  (effectiveSaving : ℚ) / ((CenterCompression.H24.m : ℚ) * (padding : ℚ))

theorem pairAggregateCount_eq : pairAggregateCount = 276 := by
  exact pairCount_eq

theorem roleCount_eq : roleCount = 20269858048 := by
  exact pairRoleCount_eq

theorem padding_eq : padding = 34359738368 := by
  exact pairPadding_eq

theorem optimisticPenalty_eq : optimisticPenalty = 2261309952 := by
  exact oneWayCodimTwoPenalty_eq

theorem effectiveSaving_eq : effectiveSaving = 163863040 := by
  rw [effectiveSaving, optimisticPenalty_eq,
    CenterCompression.H24.deltaCompressed_eq]

theorem effectiveSaving_pos : 0 < effectiveSaving := by
  rw [effectiveSaving_eq]
  norm_num

theorem normalizedSaving_eq :
    normalizedSaving = 320045 / 927712935936 := by
  norm_num [normalizedSaving, effectiveSaving_eq, padding_eq,
    CenterCompression.H24.m_eq]

theorem normalizedSaving_gt_three_point_four_e_minus_seven :
    (34 : ℚ) / 10 ^ 8 < normalizedSaving := by
  rw [normalizedSaving_eq]
  norm_num

/-- The optimistic candidate is still far above the 10^-9 target on the
    normalized scale; the missing issue is the unproved frame schedule. -/
theorem normalizedSaving_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalizedSaving := by
  rw [normalizedSaving_eq]
  norm_num

end H24
end PairDiagonalExcludedArithmetic
end ExactFourier
end OAI
