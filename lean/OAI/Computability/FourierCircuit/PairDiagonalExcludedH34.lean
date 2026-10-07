import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Basic

/-!
# Conditional diagonal-excluded pair arithmetic at `h = 34`

This is a scalar stress test for the diagonal-excluded pair-prefix idea.  It
uses the same three-point centre formulas as the `h = 24` audit, replaces the
ordered side roles by one role for each pair, and charges only one
codimension-two transition per pair aggregate across the two side stages.
The resulting arithmetic gap is above `10⁻⁹`, but the transition, source
accumulation, and target reuse schedule are not proved here.  This file is
therefore a conditional design target, not an exact DFT theorem.
-/

namespace OAI
namespace ExactFourier
namespace PairDiagonalExcludedH34

def h : ℕ := 34
def v : ℕ := Nat.choose h 3
def m : ℕ := h ^ 3
def N0 : ℕ := v ^ 3
def I0 : ℕ := 3 * v ^ 2
def pairCount : ℕ := Nat.choose h 2
def roleCount : ℕ := 2 * N0 + I0 * (pairCount + h)
def padding : ℕ := 2 ^ 39
def deltaCompressed : ℕ := 2 * N0 - 2 * I0 * h ^ 2
def pairBlock : ℕ := v ^ 2 * pairCount
def optimisticPenalty : ℕ := 2 * pairBlock
def effectiveSaving : ℕ := deltaCompressed - optimisticPenalty
def normalizedSaving : ℚ :=
  (effectiveSaving : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem h_eq : h = 34 := by rfl
theorem v_eq : v = 5984 := by norm_num [v, h, Nat.choose]
theorem m_eq : m = 39304 := by norm_num [m, h]
theorem N0_eq : N0 = 214276603904 := by
  norm_num [N0, v, h, Nat.choose]
theorem I0_eq : I0 = 107424768 := by
  norm_num [I0, v, h, Nat.choose]
theorem pairCount_eq : pairCount = 561 := by
  norm_num [pairCount, h, Nat.choose]
theorem roleCount_eq : roleCount = 492470944768 := by
  norm_num [roleCount, N0, I0, pairCount, v, h, Nat.choose]
theorem padding_eq : padding = 549755813888 := by
  norm_num [padding]
theorem padding_is_next_power : 2 ^ 38 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, N0, I0, pairCount, v, h, padding, Nat.choose]
theorem deltaCompressed_eq : deltaCompressed = 180187144192 := by
  norm_num [deltaCompressed, N0, I0, v, h, Nat.choose]
theorem pairBlock_eq : pairBlock = 20088431616 := by
  norm_num [pairBlock, pairCount, v, h, Nat.choose]
theorem optimisticPenalty_eq : optimisticPenalty = 40176863232 := by
  norm_num [optimisticPenalty, pairBlock, pairCount, v, h, Nat.choose]
theorem effectiveSaving_eq : effectiveSaving = 140010280960 := by
  norm_num [effectiveSaving, deltaCompressed, optimisticPenalty, pairBlock,
    pairCount, N0, I0, v, h, Nat.choose]
theorem effectiveSaving_pos : 0 < effectiveSaving := by
  rw [effectiveSaving_eq]
  norm_num
theorem normalizedSaving_eq : normalizedSaving = 13915 / 2147483648 := by
  norm_num [normalizedSaving, effectiveSaving_eq, m_eq, padding_eq]

/-- The conditional scalar candidate clears the target exponent scale. -/
theorem normalizedSaving_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalizedSaving := by
  rw [normalizedSaving_eq]
  norm_num

end PairDiagonalExcludedH34
end ExactFourier
end OAI
