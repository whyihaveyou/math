import OAI.Computability.FourierCircuit.SideHierarchyArithmetic
import Mathlib.Tactic.NormNum

/-!
# Optimistic near-miss audit for a pair-prefix side hierarchy

The pair-prefix construction has 276 pair aggregates and `v^2` invocations
per stage.  `SideHierarchyArithmetic` charges four residual units per pair
aggregate per stage (two directions and codimension two), giving a penalty
of `9,045,239,808` over the two stages.  This file records two deliberately
more favorable boundary fantasies:

* one transition only, while retaining codimension two;
* one transition and codimension one.

These are arithmetic stress tests, not frame constructions.  The effective
savings below are normalized against the centre-compressed padded multiplier
`W* = 2^45`; this fixed-padding comparison is useful for isolating boundary
charges, but it is not the padding of the hypothetical pair network itself.
Under the naive pair-role count, the role count is only `20,269,858,048` and
the next power is `2^35`, so the exponent must be recomputed separately.
The file therefore makes no claim that the optimistic variants miss `1e-9`.
It only isolates the conditional boundary arithmetic; a full pair result still
needs a frame-labelled stage and its actual role/padding count.
-/

namespace OAI
namespace ExactFourier
namespace PairHierarchyNearMiss
namespace H24

open CenterCompression
open SideHierarchyArithmetic.H24

def pairBlock : ℕ := invocationsPerStage * pairCount

/- Naive scalar role count if the `276` pair aggregates replace the ordered
   side bank, retaining the `h` surviving centre wires. -/
def pairRoleCount : ℕ :=
  2 * CenterCompression.H24.N0 +
    CenterCompression.H24.I0 * (pairCount + CenterCompression.H24.h)

def pairPadding : ℕ := 2 ^ 35

def oneWayCodimTwoPenalty : ℕ := 2 * pairBlock

def oneWayCodimOnePenalty : ℕ := pairBlock

def effectiveCodimTwoSaving : ℕ :=
  CenterCompression.H24.deltaCompressed - oneWayCodimTwoPenalty

def effectiveCodimOneSaving : ℕ :=
  CenterCompression.H24.deltaCompressed - oneWayCodimOnePenalty

theorem pairBlock_eq : pairBlock = 1130654976 := by
  norm_num [pairBlock, invocationsPerStage, pairCount,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem pairRoleCount_eq : pairRoleCount = 20269858048 := by
  norm_num [pairRoleCount, pairCount, h, v,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem pairPadding_eq : pairPadding = 34359738368 := by
  norm_num [pairPadding]

theorem oneWayCodimTwoPenalty_eq : oneWayCodimTwoPenalty = 2261309952 := by
  norm_num [oneWayCodimTwoPenalty, pairBlock, invocationsPerStage, pairCount,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem oneWayCodimOnePenalty_eq : oneWayCodimOnePenalty = 1130654976 := by
  norm_num [oneWayCodimOnePenalty, pairBlock, invocationsPerStage, pairCount,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem effectiveCodimTwoSaving_eq : effectiveCodimTwoSaving = 163863040 := by
  rw [effectiveCodimTwoSaving, oneWayCodimTwoPenalty_eq,
    CenterCompression.H24.deltaCompressed_eq]

theorem effectiveCodimOneSaving_eq : effectiveCodimOneSaving = 1294518016 := by
  rw [effectiveCodimOneSaving, oneWayCodimOnePenalty_eq,
    CenterCompression.H24.deltaCompressed_eq]

theorem effectiveCodimTwoSaving_lt_two_hundred_million :
    effectiveCodimTwoSaving < 200000000 := by
  rw [effectiveCodimTwoSaving, oneWayCodimTwoPenalty_eq,
    CenterCompression.H24.deltaCompressed_eq]
  norm_num

theorem effectiveCodimOneSaving_lt_one_point_three_billion :
    effectiveCodimOneSaving < 1300000000 := by
  rw [effectiveCodimOneSaving, oneWayCodimOnePenalty_eq,
    CenterCompression.H24.deltaCompressed_eq]
  norm_num

end H24
end PairHierarchyNearMiss
end ExactFourier
end OAI
