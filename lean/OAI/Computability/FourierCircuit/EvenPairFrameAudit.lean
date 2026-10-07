import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# Arithmetic certificate for target-aware even-pair grouping

The original side correction uses only intersection classes `0` and `2`.
For a target triple at `h = 24`, a conditional grouping therefore has
`choose (h - 3) 2 = 210` disjoint pairs and `choose 3 2 = 3` inside pairs.
The source script `scripts/frame_compatible_side_search.py` checks the scalar
coefficient identity and the GF(2) ranks.  This file records the resulting
role count and two explicit cost models in Lean.

The two-unit model is intentionally optimistic: it is a target for a future
frame-labelled construction, not a theorem that such a construction exists.
The codimension model charges two directions for leaving and returning to the
shared pair span.  Both statements are arithmetic conditionals and neither is
a lower bound for arbitrary side-wire networks.
-/

namespace OAI
namespace ExactFourier
namespace EvenPairFrameAudit
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
/- The 213 groups are replicated for every target triple. -/
def roleCount : ℕ := 2 * N0 + I0 * (v * groupedPairCount + h)
def padding : ℕ := 2 ^ 43
def centreSaving : ℕ := 2 * N0 - 2 * I0 * h ^ 2

def optimisticPenalty : ℕ := 2 * v ^ 3 * groupedPairCount
def optimisticMargin : ℤ := (centreSaving : ℤ) - (optimisticPenalty : ℤ)
def optimisticNormalizedMargin : ℚ :=
  (optimisticMargin : ℚ) / ((m : ℚ) * (padding : ℚ))

def codim0 : ℕ := (h - 2) - (h - 5)
def codim2 : ℕ := (h - 2) - (h - 3)
def codimensionPenalty : ℕ :=
  2 * v ^ 3 * (c0Count * codim0 + c2Count * codim2)
def codimensionMargin : ℤ := (centreSaving : ℤ) - (codimensionPenalty : ℤ)
def codimensionNormalizedMargin : ℚ :=
  (codimensionMargin : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem h_eq : h = 24 := by
  rfl

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem c0Count_eq : c0Count = 210 := by
  norm_num [c0Count, h, CenterCompression.H24.h, Nat.choose]

theorem c2Count_eq : c2Count = 3 := by
  norm_num [c2Count, Nat.choose]

theorem groupedPairCount_eq : groupedPairCount = 213 := by
  norm_num [groupedPairCount, c0Count, c2Count, h,
    CenterCompression.H24.h, Nat.choose]

theorem roleCount_eq : roleCount = 5315127110656 := by
  norm_num [roleCount, groupedPairCount, c0Count, c2Count, h, N0, I0, v,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 8796093022208 := by
  norm_num [padding]

theorem padding_is_next_power : 2 ^ 42 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, groupedPairCount, c0Count, c2Count, h, N0, I0, v,
    padding, CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  norm_num [centreSaving, N0, I0, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem optimisticPenalty_eq : optimisticPenalty = 3532166145024 := by
  norm_num [optimisticPenalty, groupedPairCount, c0Count, c2Count, v, h,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem optimisticMargin_eq : optimisticMargin = -3529740972032 := by
  norm_num [optimisticMargin, centreSaving, optimisticPenalty,
    groupedPairCount, c0Count, c2Count, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem optimisticNormalizedMargin_eq :
    optimisticNormalizedMargin = -861753167 / 29686813949952 := by
  norm_num [optimisticNormalizedMargin, optimisticMargin_eq,
    m, padding, CenterCompression.H24.m, CenterCompression.H24.h]

theorem codim0_eq : codim0 = 3 := by
  norm_num [codim0, h, CenterCompression.H24.h]

theorem codim2_eq : codim2 = 1 := by
  norm_num [codim2, h, CenterCompression.H24.h]

theorem codimensionPenalty_eq : codimensionPenalty = 10497000797184 := by
  norm_num [codimensionPenalty, c0Count, c2Count, codim0, codim2, v, h,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem codimensionMargin_eq : codimensionMargin = -10494575624192 := by
  norm_num [codimensionMargin, centreSaving, codimensionPenalty,
    c0Count, c2Count, codim0, codim2, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem codimensionNormalizedMargin_eq :
    codimensionNormalizedMargin = -640538063 / 7421703487488 := by
  norm_num [codimensionNormalizedMargin, codimensionMargin_eq,
    m, padding, CenterCompression.H24.m, CenterCompression.H24.h]

end H24
end EvenPairFrameAudit
end ExactFourier
end OAI
