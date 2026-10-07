import OAI.Computability.FourierCircuit.PairComplementAggregateBoundary
import OAI.Computability.FourierCircuit.PairComplementDisjointSpan
import OAI.Computability.FourierCircuit.PairComplementSideArithmetic
import Mathlib.Tactic

/-!
# Frame-compatible pair/complement candidate: rank and arithmetic ledger

The scalar pair/complement invocation has two target-independent pair banks:
`A_F` (triples containing `F`) and `B_F` (triples disjoint from `F`).  The
local span certificates for these banks both have rank `h - 2` at `h = 24`.
This file joins those rank facts to the aggregate-wise four-edge ledger and
records the exact width and side-role reduction.

The gate schedule is still a premise.  In particular, the rank facts do not
construct the common complex gate, the B-bank transport through all prefixes,
or the arbitrary-auxiliary restoration in the physical eight-row network.
Consequently the final `> 10⁻⁹` statement below is explicitly a conditional
arithmetic candidate, while every integer/rank equality in this file is
Lean-checked.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementFrameCompatibleCandidate

open PairComplementAggregateBoundary
open PairComplementDisjointSpan
open PairTargetFrameLocal

namespace H24

abbrev h : ℕ := 24
abbrev v : ℕ := CenterCompression.H24.v
abbrev pairCount : ℕ := Nat.choose h 2
abbrev candidateSideRoles : ℕ := 2 * pairCount
abbrev baselineSideRoles : ℕ := v * CenterCompression.H24.dNbr
abbrev candidateWidth : ℕ := PairComplementSideArithmetic.H24.roleCount
abbrev candidatePadding : ℕ := PairComplementSideArithmetic.H24.padding

/- The A-bank support is the span of all triples containing a fixed pair. -/
theorem A_bank_rank (F : Finset (Fin 24)) (hF : F.card = 2) :
    Module.finrank (ZMod 2) (pairSpan F) = 22 := by
  simpa using (pairSpan_finrank F hF)

/- The B-bank support is the span of all triples disjoint from a fixed pair. -/
theorem B_bank_rank (F : Finset (Fin 24)) (hF : F.card = 2) :
    Module.finrank (ZMod 2) (disjointTripleSpan F) = 22 := by
  exact PairComplementDisjointSpan.H24.pair_disjointTripleSpan_rank F hF

theorem candidate_and_B_bank_have_same_rank
    (F : Finset (Fin 24)) (hF : F.card = 2) :
    Module.finrank (ZMod 2) (pairSpan F) =
      Module.finrank (ZMod 2) (disjointTripleSpan F) := by
  rw [A_bank_rank F hF, B_bank_rank F hF]

theorem pairCount_eq : pairCount = 276 := by
  norm_num [pairCount, h, Nat.choose]

theorem candidateSideRoles_eq : candidateSideRoles = 552 := by
  norm_num [candidateSideRoles, pairCount_eq]

theorem baselineSideRoles_eq : baselineSideRoles = 2819432 := by
  norm_num [baselineSideRoles, v, CenterCompression.H24.v,
    CenterCompression.H24.dNbr, CenterCompression.H24.h, Nat.choose]

theorem side_role_reduction_eq :
    baselineSideRoles - candidateSideRoles = 2818880 := by
  rw [baselineSideRoles_eq, candidateSideRoles_eq]

theorem side_role_reduction_gt_thousandfold :
    1000 * candidateSideRoles < baselineSideRoles := by
  rw [baselineSideRoles_eq, candidateSideRoles_eq]
  norm_num

theorem candidateWidth_eq : candidateWidth = 23661822976 := by
  exact PairComplementSideArithmetic.H24.roleCount_eq

theorem candidatePadding_eq : candidatePadding = 34359738368 := by
  exact PairComplementSideArithmetic.H24.padding_eq

theorem candidateWidth_bounds :
    2 ^ 34 < candidateWidth ∧ candidateWidth ≤ candidatePadding := by
  rw [candidateWidth_eq, candidatePadding_eq]
  norm_num

theorem candidateWidth_lt_centreCompressedWidth :
    candidateWidth < CenterCompression.H24.Wcompressed := by
  rw [candidateWidth_eq, CenterCompression.H24.Wcompressed_eq]
  norm_num

/- The aggregate-wise route has one block per pair-bank aggregate. -/
abbrev aggregateCount : ℕ := 2 * pairCount
abbrev aggregateThreeStageCost : ℕ :=
  aggregateCount * PairComplementAggregateBoundary.H24.threeStageCost

theorem aggregateCount_eq : aggregateCount = 552 := by
  norm_num [aggregateCount, pairCount_eq]

theorem aggregateThreeStageCost_eq : aggregateThreeStageCost = 7962048 := by
  rw [aggregateThreeStageCost, aggregateCount_eq,
    PairComplementAggregateBoundary.H24.threeStageCost_eq]

theorem aggregateStageCost_per_bank_eq (e : ℕ) (he : 1 ≤ e) :
    PairComplementAggregateBoundary.aggregateStageCost e h = e * h := by
  exact PairComplementAggregateBoundary.aggregateStageCost_eq he (by norm_num [h])

theorem aggregate_three_stage_cost_formula :
    PairComplementAggregateBoundary.H24.threeStageCost = 14424 := by
  exact PairComplementAggregateBoundary.H24.threeStageCost_eq

/- This is the finite rank/ledger premise that a future gate proof must realize. -/
def FrameCompatibleLedgerPremise : Prop :=
  (∀ F : Finset (Fin 24), F.card = 2 →
      Module.finrank (ZMod 2) (pairSpan F) = 22) ∧
  (∀ F : Finset (Fin 24), F.card = 2 →
      Module.finrank (ZMod 2) (disjointTripleSpan F) = 22) ∧
  (∀ e : ℕ, 1 ≤ e →
      PairComplementAggregateBoundary.aggregateStageCost e h = e * h)

theorem frameCompatibleLedgerPremise_arithmetic : FrameCompatibleLedgerPremise := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    exact A_bank_rank F hF
  · intro F hF
    exact B_bank_rank F hF
  · intro e he
    exact aggregateStageCost_per_bank_eq e he

/- The pair/complement scalar denominator gives a large conditional candidate gap. -/
theorem conditional_normalized_candidate_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < PairComplementSideArithmetic.H24.normalized := by
  exact PairComplementAggregateBoundary.H24.candidate_normalized_gt_one_e_minus_nine

theorem conditional_normalized_candidate_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < PairComplementSideArithmetic.H24.normalized := by
  exact PairComplementSideArithmetic.H24.normalized_gt_one_e_minus_six

end H24
end PairComplementFrameCompatibleCandidate
end ExactFourier
end OAI
