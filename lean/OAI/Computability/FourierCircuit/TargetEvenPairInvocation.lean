import OAI.Computability.FourierCircuit.CompressedInvocation
import Mathlib.Tactic

/-!
# Target-aware even-pair scalar invocation (research candidate)

For a target triple `S`, the two nonzero side classes are `|S ∩ T| = 0`
and `|S ∩ T| = 2`.  This file groups the corresponding source sums by pairs
inside the target or disjoint from the target.  The grouping is deliberately
target-indexed: it is an exact scalar candidate, not a target-independent
physical side bank.  The companion finite audit records its frame ranks and
conditional costs.

The result below proves the scalar `RG + J V = I` identity and the generic
forward/inverse/three-invocation restoration laws.  It does not assert a
frame-labelled gate schedule or an all-length recurrence.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace TargetEvenPairInvocation

open CenterCompression
open CompressedInvocation

private def pairSet (h : ℕ) : Finset (Finset (Fin h)) :=
  Finset.powersetCard 2 (Finset.univ : Finset (Fin h))

private abbrev Triple (h : ℕ) := CenterCompression.Triple h

private lemma pair_filter_subset (h : ℕ) (U : Finset (Fin h)) :
    (pairSet h).filter (fun F => F ⊆ U) = Finset.powersetCard 2 U := by
  ext F
  simp only [pairSet, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hsub⟩
    exact ⟨hsub, hcard⟩
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨Finset.subset_univ _, hcard⟩, hsub⟩

private lemma pair_count_subset (h : ℕ) (U : Finset (Fin h)) :
    ((pairSet h).filter (fun F => F ⊆ U)).card = U.card.choose 2 := by
  rw [pair_filter_subset]
  exact Finset.card_powersetCard 2 U

private lemma pair_sum_subset {h : ℕ} {K : Type*} [Field K]
    (U : Finset (Fin h)) (z : K) :
    (∑ F ∈ pairSet h, if F ⊆ U then z else 0) =
      (U.card.choose 2 : K) * z := by
  have hfilter :
      {F ∈ pairSet h | F ⊆ U} = (pairSet h).filter (fun F => F ⊆ U) := by
    rfl
  calc
    (∑ F ∈ pairSet h, if F ⊆ U then z else 0) =
        (∑ F ∈ pairSet h, if F ⊆ U then (1 : K) else 0) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hFU : F ⊆ U <;> simp [hFU]
    _ = (({F ∈ pairSet h | F ⊆ U}.card : ℕ) : K) * z := by
      rw [Finset.sum_boole]
    _ = (U.card.choose 2 : K) * z := by
      rw [hfilter, pair_count_subset]

section H24

abbrev H : ℕ := 24
abbrev Source := Triple H
abbrev PairBank (K : Type*) := Finset (Fin H) → K × K
abbrev TargetBank (K : Type*) := Source → PairBank K

variable {K : Type*} [Field K] [CharZero K]

/-- Target-indexed pair aggregates for the `r=0` and `r=2` classes. -/
def targetAggregates (x : Source → K) (S : Source)
    (F : Finset (Fin H)) : K × K :=
  (∑ T ∈ (tripleSet H).attach,
      if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0,
   ∑ T ∈ (tripleSet H).attach,
      if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)

def targetInput (x : Source → K) : TargetBank K :=
  fun S => targetAggregates x S

/-- Read the disjoint-pair and target-pair banks with the exact side weights. -/
def targetRead (a : TargetBank K) (S : Source) : K :=
  (1 / 6 : K) * (∑ F ∈ pairSet H,
      if Disjoint F S.1 then (a S F).1 else 0) -
    (1 / 2 : K) * (∑ F ∈ pairSet H,
      if F ⊆ S.1 then (a S F).2 else 0)

noncomputable def targetReadHom : TargetBank K →+ (Source → K) where
  toFun := targetRead
  map_zero' := by
    funext S
    simp [targetRead]
  map_add' := by
    intro a b
    funext S
    simp only [targetRead, Pi.add_apply, Prod.fst_add, Prod.snd_add]
    have hdis :
        (∑ F ∈ pairSet H,
          if Disjoint F S.1 then (a S F).1 + (b S F).1 else 0) =
          (∑ F ∈ pairSet H,
            if Disjoint F S.1 then (a S F).1 else 0) +
            ∑ F ∈ pairSet H,
              if Disjoint F S.1 then (b S F).1 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hFS : Disjoint F S.1 <;> simp [hFS]
    have hsub :
        (∑ F ∈ pairSet H,
          if F ⊆ S.1 then (a S F).2 + (b S F).2 else 0) =
          (∑ F ∈ pairSet H,
            if F ⊆ S.1 then (a S F).2 else 0) +
            ∑ F ∈ pairSet H,
              if F ⊆ S.1 then (b S F).2 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hFS : F ⊆ S.1 <;> simp [hFS]
    rw [hdis, hsub]
    ring

noncomputable def targetInputHom : (Source → K) →+ TargetBank K where
  toFun := targetInput
  map_zero' := by
    funext S F
    simp [targetInput, targetAggregates]
  map_add' := by
    intro x y
    funext S F
    apply Prod.ext <;>
      simp only [targetInput, targetAggregates, Pi.add_apply, Prod.add_def]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hT0 : F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅
      · simp [Finset.card_eq_zero, hT0]
      · simp [Finset.card_eq_zero, hT0]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hT2 : F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 <;> simp [hT2]

private theorem targetRead_targetAggregates (x : Source → K) (S : Source) :
    targetRead (targetInput x) S =
      ∑ T ∈ (tripleSet H).attach,
        (if S.1 ∩ T.1 = ∅ then (1 / 2 : K) * x T
         else if (S.1 ∩ T.1).card = 2 then -(1 / 2 : K) * x T
         else 0) := by
  unfold targetRead targetInput targetAggregates
  have h0 :
      (∑ F ∈ pairSet H,
        if Disjoint F S.1 then
          (∑ T ∈ (tripleSet H).attach,
            if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
          else 0) =
        ∑ T ∈ (tripleSet H).attach,
          if S.1 ∩ T.1 = ∅ then (3 : K) * x T else 0 := by
    calc
      (∑ F ∈ pairSet H,
        if Disjoint F S.1 then
          (∑ T ∈ (tripleSet H).attach,
            if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
          else 0) =
          ∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
            if Disjoint F S.1 then
              (if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
              else 0 := by
                apply Finset.sum_congr rfl
                intro F hF
                by_cases hFS : Disjoint F S.1 <;> simp [hFS]
      _ = ∑ T ∈ (tripleSet H).attach, ∑ F ∈ pairSet H,
            if Disjoint F S.1 then
              (if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
              else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ T ∈ (tripleSet H).attach,
            if S.1 ∩ T.1 = ∅ then
              (3 : K) * x T else 0 := by
                apply Finset.sum_congr rfl
                intro T hT
                by_cases hinter : S.1 ∩ T.1 = ∅
                · have hbody (F : Finset (Fin H)) :
                      (if Disjoint F S.1 then
                          (if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
                        else 0) =
                        (if F ⊆ T.1 then x T else 0) := by
                    by_cases hFT : F ⊆ T.1
                    · have hdis : Disjoint F S.1 := by
                        apply Finset.disjoint_left.2
                        intro i hiF hiS
                        have hiT : i ∈ T.1 := hFT hiF
                        have hiI : i ∈ S.1 ∩ T.1 := Finset.mem_inter.2 ⟨hiS, hiT⟩
                        rw [hinter] at hiI
                        simpa using hiI
                      calc
                        (if Disjoint F S.1 then
                            (if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0)
                          else 0) =
                            if F ⊆ T.1 ∧ S.1 ∩ T.1 = ∅ then x T else 0 := by
                              rw [if_pos hdis]
                        _ = x T := by rw [if_pos ⟨hFT, hinter⟩]
                        _ = if F ⊆ T.1 then x T else 0 := by rw [if_pos hFT]
                    · simp [hFT]
                  simp_rw [hbody]
                  rw [pair_sum_subset T.1 (x T)]
                  simp [triple_card T, hinter]
                · simp [hinter]
  have h2 :
      (∑ F ∈ pairSet H,
        if F ⊆ S.1 then
          (∑ T ∈ (tripleSet H).attach,
            if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)
          else 0) =
        ∑ T ∈ (tripleSet H).attach,
          if (S.1 ∩ T.1).card = 2 then x T else 0 := by
    calc
      (∑ F ∈ pairSet H,
        if F ⊆ S.1 then
          (∑ T ∈ (tripleSet H).attach,
            if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)
          else 0) =
          ∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
            if F ⊆ S.1 then
              (if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)
              else 0 := by
                apply Finset.sum_congr rfl
                intro F hF
                by_cases hFS : F ⊆ S.1 <;> simp [hFS]
      _ = ∑ T ∈ (tripleSet H).attach, ∑ F ∈ pairSet H,
            if F ⊆ S.1 then
              (if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)
              else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ T ∈ (tripleSet H).attach,
            if (S.1 ∩ T.1).card = 2 then x T else 0 := by
                apply Finset.sum_congr rfl
                intro T hT
                by_cases htwo : (S.1 ∩ T.1).card = 2
                · have hbody (F : Finset (Fin H)) :
                      (if F ⊆ S.1 then
                          (if F ⊆ T.1 ∧ (S.1 ∩ T.1).card = 2 then x T else 0)
                        else 0) =
                        (if F ⊆ S.1 ∩ T.1 then x T else 0) := by
                    have hiff :
                        (F ⊆ S.1 ∧ F ⊆ T.1) ↔ F ⊆ S.1 ∩ T.1 := by
                      constructor
                      · intro h
                        exact Finset.subset_inter h.1 h.2
                      · intro hI
                        refine ⟨?_, ?_⟩
                        · intro i hi
                          exact (Finset.mem_inter.1 (hI hi)).1
                        · intro i hi
                          exact (Finset.mem_inter.1 (hI hi)).2
                    by_cases hFS : F ⊆ S.1
                    · by_cases hFT : F ⊆ T.1
                      · have hI : F ⊆ S.1 ∩ T.1 := hiff.mp ⟨hFS, hFT⟩
                        simp [hFS, hFT, hI, htwo]
                      · have hI : ¬ F ⊆ S.1 ∩ T.1 := by
                          intro hI
                          exact hFT (fun i hi => (Finset.mem_inter.1 (hI hi)).2)
                        simp [hFS, hFT, hI, htwo]
                    · have hI : ¬ F ⊆ S.1 ∩ T.1 := by
                        intro hI
                        exact hFS (fun i hi => (Finset.mem_inter.1 (hI hi)).1)
                      simp [hFS, hI, htwo]
                  simp_rw [hbody]
                  have hcount := pair_sum_subset (S.1 ∩ T.1) (x T)
                  simpa [htwo] using hcount
                · simp [htwo]
  rw [h0, h2]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hinter : S.1 ∩ T.1 = ∅
  · have hzero : (S.1 ∩ T.1).card = 0 := Finset.card_eq_zero.mpr hinter
    simp [hinter, hzero]
    ring
  · by_cases htwo : (S.1 ∩ T.1).card = 2
    · simp [hinter, htwo]
    · simp [hinter, htwo]

theorem targetRead_identity (x : Source → K) :
    CompressedInvocation.OrderedPairs.RHom
          (compressedG x) + targetReadHom (targetInputHom x) = x := by
  funext S
  change compressedR S (compressedG x) + targetRead (targetInput x) S = x S
  have hside : targetRead (targetInput x) S = sideAction S x := by
    rw [targetRead_targetAggregates]
    unfold sideAction sideCoeff
    apply Finset.sum_congr rfl
    intro T hT
    by_cases heq : S = T
    · subst T
      have hne : S.1 ≠ ∅ := by
        intro hS
        have hc := triple_card S
        simp [hS] at hc
      simp [triple_card S, hne]
    · have hlt := inter_card_lt_three S T heq
      have hle : (S.1 ∩ T.1).card ≤ 3 :=
        le_trans (Nat.le_of_lt_succ hlt) (by omega)
      by_cases hinter : S.1 ∩ T.1 = ∅
      · simp [hinter, heq]
      have hcard0 : (S.1 ∩ T.1).card ≠ 0 := by
        intro hzero
        exact hinter (Finset.card_eq_zero.mp hzero)
      interval_cases hr : (S.1 ∩ T.1).card
      · exfalso
        apply hcard0
        simpa using hr
      · have hne : S.1 ∩ T.1 ≠ ∅ := hinter
        simp [hr, heq, hne]
      · simp [hr, heq, hinter] <;> try ring
  rw [hside]
  exact compressed_plus_side S x

theorem forward_restore
    (s : CompressedInvocation.State (Source → K) (TargetBank K) (Fin H → K)) :
    CompressedInvocation.eightRows
        CompressedInvocation.OrderedPairs.RHom
        compressedG
        targetReadHom
        targetInputHom s = {s with y := s.y + s.x} := by
  exact @CompressedInvocation.eightRows_restore (Source → K) (TargetBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom compressedG
    targetReadHom targetInputHom targetRead_identity s

theorem inverse_restore
    (s : CompressedInvocation.State (Source → K) (TargetBank K) (Fin H → K)) :
    CompressedInvocation.inverseEightRows
        CompressedInvocation.OrderedPairs.RHom
        compressedG
        targetReadHom
        targetInputHom s = {s with y := s.y - s.x} := by
  exact @CompressedInvocation.inverseEightRows_restore (Source → K) (TargetBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom compressedG
    targetReadHom targetInputHom targetRead_identity s

theorem three_exchange
    (s : CompressedInvocation.State (Source → K) (TargetBank K) (Fin H → K)) :
    CompressedInvocation.threeInvocations
        CompressedInvocation.OrderedPairs.RHom
        compressedG
        targetReadHom
        targetInputHom s = {s with x := -s.y, y := s.x} := by
  exact @CompressedInvocation.threeInvocations_exchange (Source → K) (TargetBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom compressedG
    targetReadHom targetInputHom targetRead_identity s

end H24
end TargetEvenPairInvocation
end ExactFourier
end OAI
