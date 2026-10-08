import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Residual-rank arithmetic for the redundant-global side-moment candidate

The redundant-global candidate keeps 24 incidence channels and 24 compressed
centre channels. Any correction factored through those channels has rank at
most 48 on the 2024-dimensional triple space. The generic rank interface in
`RankComplementLowerBound.lean` therefore leaves at least 1976 direct residual
channels. The charge below is deliberately conditional: it assumes one (or
two) frame units per independent direct residual channel and is not a lower
bound for arbitrary dense gates.
-/

namespace OAI
namespace ExactFourier
namespace SideMomentRankFloorArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m
def centreChannels : ℕ := h
def sideChannels : ℕ := h
def totalChannels : ℕ := centreChannels + sideChannels
def residualRank : ℕ := v - totalChannels
def oneWayPenalty : ℕ := I0 * residualRank
def twoWayPenalty : ℕ := 2 * oneWayPenalty
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def oneWayMargin : ℤ := (centreSaving : ℤ) - (oneWayPenalty : ℤ)
def twoWayMargin : ℤ := (centreSaving : ℤ) - (twoWayPenalty : ℤ)
def normalizedTwoWay : ℚ :=
  (twoWayMargin : ℚ) / ((m : ℚ) * (2 ^ 34 : ℕ))

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem channel_count_eq : totalChannels = 48 := by
  norm_num [totalChannels, centreChannels, sideChannels, h,
    CenterCompression.H24.h]

theorem residualRank_eq : residualRank = 1976 := by
  norm_num [residualRank, v, totalChannels, centreChannels, sideChannels,
    h, CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem oneWayPenalty_eq : oneWayPenalty = 24284502528 := by
  norm_num [oneWayPenalty, residualRank, I0, v, totalChannels,
    centreChannels, sideChannels, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem twoWayPenalty_eq : twoWayPenalty = 48569005056 := by
  norm_num [twoWayPenalty, oneWayPenalty, residualRank, I0, v,
    totalChannels, centreChannels, sideChannels, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem oneWayMargin_eq : oneWayMargin = -21859329536 := by
  norm_num [oneWayMargin, centreSaving, oneWayPenalty,
    CenterCompression.H24.deltaCompressed, residualRank, I0, v,
    totalChannels, centreChannels, sideChannels, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem twoWayMargin_eq : twoWayMargin = -46143832064 := by
  norm_num [twoWayMargin, centreSaving, twoWayPenalty, oneWayPenalty,
    CenterCompression.H24.deltaCompressed, residualRank, I0, v,
    totalChannels, centreChannels, sideChannels, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem oneWayMargin_neg : oneWayMargin < 0 := by
  rw [oneWayMargin_eq]
  norm_num

theorem twoWayMargin_neg : twoWayMargin < 0 := by
  rw [twoWayMargin_eq]
  norm_num

theorem normalizedTwoWay_eq :
    normalizedTwoWay = -704099 / 3623878656 := by
  norm_num [normalizedTwoWay, twoWayMargin_eq, m,
    CenterCompression.H24.m, CenterCompression.H24.h]

theorem normalizedTwoWay_neg : normalizedTwoWay < 0 := by
  rw [normalizedTwoWay_eq]
  norm_num

end H24
end SideMomentRankFloorArithmetic
end ExactFourier
end OAI
