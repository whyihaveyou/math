import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Corrected arithmetic for target-indexed even-pair aggregates

The earlier `TargetEvenPairArithmetic` ledger counted 213 pair groups per
invocation.  Those are 210 + 3 groups **for each target triple** `S`; the
original invocation has `v` targets (the paper's side-wire count is
`v * dNbr`).  This file keeps the same conditional cost model but inserts that
missing factor `v`.  It is an arithmetic audit only; it does not assert a
frame-labelled circuit or a universal lower bound.
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

def c0Count : ℕ := Nat.choose (h - 3) 2
def c2Count : ℕ := Nat.choose 3 2
def groupedPairCount : ℕ := c0Count + c2Count

/- There are `v` target triples, each carrying all 213 groups. -/
def rolesPerInvocation : ℕ := v * groupedPairCount
def roleCount : ℕ := 2 * N0 + I0 * (rolesPerInvocation + h)
def padding : ℕ := 2 ^ 43

def centreSaving : ℕ := CenterCompression.H24.deltaCompressed

/- The old optimistic charge is `2 * v^2 * 213`; target indexing adds `v`. -/
def optimisticPenalty : ℕ := 2 * v ^ 2 * rolesPerInvocation
def optimisticMargin : ℤ := (centreSaving : ℤ) - (optimisticPenalty : ℤ)

/- Codimension costs are 3 for each C0 group and 1 for each C2 group. -/
def codimPenalty : ℕ :=
  2 * v ^ 2 * v * (c0Count * 3 + c2Count * 1)
def codimMargin : ℤ := (centreSaving : ℤ) - (codimPenalty : ℤ)

def normalizedMargin : ℚ :=
  (optimisticMargin : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem c0Count_eq : c0Count = 210 := by
  norm_num [c0Count, h, CenterCompression.H24.h, Nat.choose]

theorem c2Count_eq : c2Count = 3 := by
  norm_num [c2Count]

theorem groupedPairCount_eq : groupedPairCount = 213 := by
  norm_num [groupedPairCount, c0Count, c2Count, h,
    CenterCompression.H24.h, Nat.choose]

theorem rolesPerInvocation_eq : rolesPerInvocation = 431112 := by
  rw [rolesPerInvocation, groupedPairCount_eq]
  norm_num [v, CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem roleCount_eq : roleCount = 5315127110656 := by
  norm_num [roleCount, rolesPerInvocation, groupedPairCount, c0Count, c2Count,
    h, v, N0, I0, CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 8796093022208 := by
  norm_num [padding]

theorem padding_bounds : 2 ^ 42 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, rolesPerInvocation, groupedPairCount, c0Count, c2Count,
    h, v, N0, I0, padding, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem optimisticPenalty_eq : optimisticPenalty = 3532166145024 := by
  norm_num [optimisticPenalty, rolesPerInvocation, groupedPairCount,
    c0Count, c2Count, v, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem optimisticMargin_eq : optimisticMargin = -3529740972032 := by
  norm_num [optimisticMargin, centreSaving_eq, optimisticPenalty_eq]

theorem codimPenalty_eq : codimPenalty = 10497000797184 := by
  norm_num [codimPenalty, c0Count, c2Count, v, h,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem codimMargin_eq : codimMargin = -10494575624192 := by
  norm_num [codimMargin, centreSaving_eq, codimPenalty_eq]

theorem normalizedMargin_eq :
    normalizedMargin = -861753167 / 29686813949952 := by
  norm_num [normalizedMargin, optimisticMargin_eq, padding_eq,
    m, CenterCompression.H24.m, CenterCompression.H24.h]

theorem corrected_margin_negative : optimisticMargin < 0 := by
  rw [optimisticMargin_eq]
  norm_num

end H24
end TargetEvenPairArithmetic
end ExactFourier
end OAI
