import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Arithmetic certificate for the target-aware even-pair candidate

This file records the exact h=24 ledger for the target-indexed even-pair
grouping formalized in `TargetEvenPairInvocation`.  It separates the
optimistic two-direction charge from the codimension-weighted charge.  The
former is positive, while the latter is negative; neither number is asserted
to be a physical all-length circuit bound.
-/

namespace OAI
namespace ExactFourier
namespace TargetEvenPairArithmetic

namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m

def disjointPairCount : ℕ := Nat.choose (h - 3) 2
def targetPairCount : ℕ := Nat.choose 3 2
def groupedPairCount : ℕ := disjointPairCount + targetPairCount

def roleCount : ℕ := 2 * N0 + I0 * (groupedPairCount + h)
def padding : ℕ := 2 ^ 35
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def optimisticPenalty : ℕ := 2 * v ^ 2 * groupedPairCount
def optimisticMargin : ℤ := centreSaving - optimisticPenalty
def codimPenalty : ℕ := 2 * v ^ 2 * (3 * disjointPairCount + targetPairCount)
def codimMargin : ℤ := centreSaving - codimPenalty
def optimisticNormalized : ℚ := (optimisticMargin : ℚ) / ((m : ℚ) * padding)
def codimNormalized : ℚ := (codimMargin : ℚ) / ((m : ℚ) * padding)

theorem disjointPairCount_eq : disjointPairCount = 210 := by
  norm_num [disjointPairCount, h, CenterCompression.H24.h, Nat.choose]

theorem targetPairCount_eq : targetPairCount = 3 := by
  norm_num [targetPairCount]

theorem groupedPairCount_eq : groupedPairCount = 213 := by
  norm_num [groupedPairCount, disjointPairCount_eq, targetPairCount_eq]

theorem roleCount_eq : roleCount = 19495605184 := by
  unfold roleCount
  rw [show N0 = 8291469824 by exact CenterCompression.H24.N0_eq,
    show I0 = 12289728 by exact CenterCompression.H24.I0_eq,
    show h = 24 by rfl, groupedPairCount_eq]

theorem padding_eq : padding = 34359738368 := by
  norm_num [padding]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem optimisticPenalty_eq : optimisticPenalty = 1745141376 := by
  unfold optimisticPenalty
  rw [show v = 2024 by exact CenterCompression.H24.v_eq,
    groupedPairCount_eq]
  norm_num [optimisticPenalty]

theorem optimisticMargin_eq : optimisticMargin = 680031616 := by
  norm_num [optimisticMargin, centreSaving_eq, optimisticPenalty_eq]

theorem codimPenalty_eq : codimPenalty = 5186265216 := by
  unfold codimPenalty
  rw [show v = 2024 by exact CenterCompression.H24.v_eq,
    disjointPairCount_eq, targetPairCount_eq]
  norm_num [codimPenalty]

theorem codimMargin_eq : codimMargin = -2761092224 := by
  norm_num [codimMargin, centreSaving_eq, codimPenalty_eq]

theorem optimisticNormalized_eq :
    optimisticNormalized = 5312747 / 3710851743744 := by
  norm_num [optimisticNormalized, optimisticMargin_eq, padding_eq, m,
    CenterCompression.H24.m_eq]

theorem codimNormalized_eq :
    codimNormalized = -21571033 / 3710851743744 := by
  norm_num [codimNormalized, codimMargin_eq, padding_eq, m,
    CenterCompression.H24.m_eq]

theorem optimisticNormalized_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < optimisticNormalized := by
  rw [optimisticNormalized_eq]
  norm_num

theorem codimNormalized_lt_zero : codimNormalized < 0 := by
  rw [codimNormalized_eq]
  norm_num

end H24

end TargetEvenPairArithmetic
end ExactFourier
end OAI
