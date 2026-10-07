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

These are arithmetic stress tests, not frame constructions.  Even the second
fantasy leaves less than 1.3e9 effective saving, far below the approximately
4.637e9 saving needed for a 1e-9 exponent gap at the H=24 padded multiplier.
Thus changing only persistence or codimension in this pair hierarchy cannot
reach the requested scale; a successful route needs a different factorization
or a genuinely new stage boundary.
-/

namespace OAI
namespace ExactFourier
namespace PairHierarchyNearMiss
namespace H24

open CenterCompression
open SideHierarchyArithmetic.H24

def pairBlock : ℕ := invocationsPerStage * pairCount

def oneWayCodimTwoPenalty : ℕ := 2 * pairBlock

def oneWayCodimOnePenalty : ℕ := pairBlock

def effectiveCodimTwoSaving : ℕ :=
  CenterCompression.H24.deltaCompressed - oneWayCodimTwoPenalty

def effectiveCodimOneSaving : ℕ :=
  CenterCompression.H24.deltaCompressed - oneWayCodimOnePenalty

theorem pairBlock_eq : pairBlock = 1130654976 := by
  norm_num [pairBlock, invocationsPerStage, pairCount,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

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
