import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Conditional price of one shared pair-bank frame

The joint-join certificate shows that a common frame for the target pair
aggregates has full active dimension 24, while one fixed pair bank has rank 22.
This file records the resulting exact arithmetic under the explicit
one-direction-unit-per-invocation charge.  It is a route-specific accounting
statement, not a lower bound for arbitrary complex circuits.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementSharedJoinPrice

namespace H24

abbrev invocationCount : ℕ := CenterCompression.H24.I0
abbrev aggregateCount : ℕ := 2 * Nat.choose 24 2
abbrev rankGap : ℕ := 24 - 22
abbrev centreSaving : ℕ := CenterCompression.H24.deltaCompressed

def sharedJoinPenalty : ℕ := invocationCount * aggregateCount * rankGap
def sharedJoinMargin : ℤ := (centreSaving : ℤ) - (sharedJoinPenalty : ℤ)

theorem invocationCount_eq : invocationCount = 12289728 := by
  exact CenterCompression.H24.I0_eq

theorem aggregateCount_eq : aggregateCount = 552 := by
  norm_num [aggregateCount, Nat.choose]

theorem rankGap_eq : rankGap = 2 := by
  norm_num [rankGap]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem sharedJoinPenalty_eq : sharedJoinPenalty = 13567859712 := by
  norm_num [sharedJoinPenalty, invocationCount, aggregateCount, rankGap,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem sharedJoinPenalty_exceeds_centreSaving :
    centreSaving ≤ sharedJoinPenalty := by
  norm_num [sharedJoinPenalty, centreSaving, invocationCount, aggregateCount,
    rankGap, CenterCompression.H24.deltaCompressed,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem sharedJoinMargin_eq : sharedJoinMargin = -11142686720 := by
  norm_num [sharedJoinMargin, sharedJoinPenalty_eq, centreSaving_eq]

end H24
end PairComplementSharedJoinPrice
end ExactFourier
end OAI
