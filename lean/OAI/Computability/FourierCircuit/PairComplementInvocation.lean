import OAI.Computability.FourierCircuit.CompressedInvocation
import OAI.Computability.FourierCircuit.PairComplementSideArithmetic
import Mathlib.Tactic

/-!
# Pair/complement scalar invocation (research candidate)

For `h = 24`, this module formalizes the scalar pair/complement aggregate
proposal.  A pair bank has the two coordinates
`A_F = sum_{F subset T} x_T` and `B_F = sum_{F disjoint T} x_T` for every
2-subset `F`.  The readout uses the target-dependent `A` and `B` families and
the global moment `sum_F A_F`.  The diagonal source coordinate is carried by
an explicit direct bank: the pair expression is diagonal-free, with coefficient
`(1-r)/2`, so the direct coordinate is needed to correct the `r=3` term.

The exact scalar shears and arbitrary-bank restoration are proved through the
common `CompressedInvocation` interface.  No frame labels, physical schedule,
or all-length recursive circuit are claimed here.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace PairComplementInvocation

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

private lemma pair_filter_disjoint (h : ℕ) (U : Finset (Fin h)) :
    (pairSet h).filter (fun F => Disjoint F U) = Finset.powersetCard 2 Uᶜ := by
  ext F
  simp only [pairSet, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_compl]
  constructor
  · rintro ⟨hF, hdis⟩
    refine ⟨?_, hF.2⟩
    intro x hx
    have : x ∉ U := by
      intro hxu
      exact Finset.disjoint_left.1 hdis hx hxu
    simpa using this
  · rintro ⟨hF, hcard⟩
    refine ⟨⟨Finset.Subset.trans hF (Finset.subset_univ _), hcard⟩, ?_⟩
    exact Finset.disjoint_left.2
      (by intro x hx hxu; exact Finset.mem_compl.mp (hF hx) hxu)

private lemma pair_count_disjoint (h : ℕ) (U : Finset (Fin h)) :
    ((pairSet h).filter (fun F => Disjoint F U)).card = Uᶜ.card.choose 2 := by
  rw [pair_filter_disjoint]
  exact Finset.card_powersetCard 2 Uᶜ

private lemma sum_pair_both {h : ℕ} {K : Type*} [Field K]
    (S T : Triple h) (z : K) :
    (∑ F ∈ pairSet h,
      if F ⊆ S.1 then (if F ⊆ T.1 then z else 0) else 0) =
      ((S.1 ∩ T.1).card.choose 2 : K) * z := by
  have hbody (F : Finset (Fin h)) :
      (if F ⊆ S.1 then (if F ⊆ T.1 then z else 0) else 0) =
        (if F ⊆ S.1 ∧ F ⊆ T.1 then z else 0) := by
    by_cases hS : F ⊆ S.1 <;> by_cases hT : F ⊆ T.1 <;> simp [hS, hT]
  simp_rw [hbody]
  have hfilter :
      {F ∈ pairSet h | F ⊆ S.1 ∧ F ⊆ T.1} =
        (pairSet h).filter (fun F => F ⊆ S.1 ∩ T.1) := by
    ext F
    simp only [pairSet, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hS, hT⟩
      exact ⟨⟨Finset.subset_univ _, hcard⟩, Finset.subset_inter hS hT⟩
    · rintro ⟨⟨_, hcard⟩, hST⟩
      exact ⟨⟨Finset.subset_univ _, hcard⟩,
        Finset.Subset.trans hST Finset.inter_subset_left,
        Finset.Subset.trans hST Finset.inter_subset_right⟩
  calc
    (∑ F ∈ pairSet h, if F ⊆ S.1 ∧ F ⊆ T.1 then z else 0) =
        (∑ F ∈ pairSet h, if F ⊆ S.1 ∧ F ⊆ T.1 then (1 : K) else 0) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hp : F ⊆ S.1 ∧ F ⊆ T.1 <;> simp [hp]
    _ = (({F ∈ pairSet h | F ⊆ S.1 ∧ F ⊆ T.1}.card : ℕ) : K) * z := by
      rw [Finset.sum_boole]
    _ = ((S.1 ∩ T.1).card.choose 2 : K) * z := by
      rw [hfilter, pair_count_subset]

private lemma sum_pair_disjoint {h : ℕ} {K : Type*} [Field K]
    (S T : Triple h) (z : K) :
    (∑ F ∈ pairSet h,
      if Disjoint F S.1 then (if Disjoint F T.1 then z else 0) else 0) =
      ((Finset.univ : Finset (Fin h)).card - (S.1 ∪ T.1).card).choose 2 * z := by
  have hbody (F : Finset (Fin h)) :
      (if Disjoint F S.1 then (if Disjoint F T.1 then z else 0) else 0) =
        (if Disjoint F S.1 ∧ Disjoint F T.1 then z else 0) := by
    by_cases hS : Disjoint F S.1 <;> by_cases hT : Disjoint F T.1 <;> simp [hS, hT]
  simp_rw [hbody]
  have hfilter :
      {F ∈ pairSet h | Disjoint F S.1 ∧ Disjoint F T.1} =
        (pairSet h).filter (fun F => Disjoint F (S.1 ∪ T.1)) := by
    ext F
    simp only [pairSet, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hS, hT⟩
      exact ⟨⟨Finset.subset_univ _, hcard⟩,
        Finset.disjoint_union_right.2 ⟨hS, hT⟩⟩
    · rintro ⟨⟨_, hcard⟩, hST⟩
      refine ⟨⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
      · exact Finset.disjoint_left.2 (by
          intro x hx hxs
          exact (Finset.disjoint_left.1 hST hx)
            (Finset.mem_union_left _ hxs))
      · exact Finset.disjoint_left.2 (by
          intro x hx hxt
          exact (Finset.disjoint_left.1 hST hx)
            (Finset.mem_union_right _ hxt))
  calc
    (∑ F ∈ pairSet h, if Disjoint F S.1 ∧ Disjoint F T.1 then z else 0) =
        (∑ F ∈ pairSet h, if Disjoint F S.1 ∧ Disjoint F T.1 then (1 : K) else 0) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hp : Disjoint F S.1 ∧ Disjoint F T.1 <;> simp [hp]
    _ = (({F ∈ pairSet h | Disjoint F S.1 ∧ Disjoint F T.1}.card : ℕ) : K) * z := by
      rw [Finset.sum_boole]
    _ = (((Finset.univ : Finset (Fin h)).card - (S.1 ∪ T.1).card).choose 2 : K) * z := by
      rw [hfilter, pair_count_disjoint, Finset.card_compl]
      simp only [Finset.card_univ, Fintype.card_fin]

section H24

abbrev H : ℕ := 24
abbrev Source := Triple H
abbrev PairBank (K : Type*) := Finset (Fin H) → K × K
abbrev AggregateBank (K : Type*) := PairBank K × (Source → K)

variable {K : Type*} [Field K] [CharZero K]

/-- Two scalar aggregates carried by one pair role. -/
def pairAggregates (x : Source → K) (F : Finset (Fin H)) : K × K :=
  (∑ T ∈ (tripleSet H).attach, if F ⊆ T.1 then x T else 0,
   ∑ T ∈ (tripleSet H).attach, if Disjoint F T.1 then x T else 0)

/-- Pair aggregates plus the direct diagonal coordinate used by the scalar route. -/
def aggregateInput (x : Source → K) : AggregateBank K :=
  (pairAggregates x, x)

/-- The target-dependent pair/complement readout, including its global A moment. -/
def pairRead (a : PairBank K) (S : Source) : K :=
  ((∑ F ∈ pairSet H, if F ⊆ S.1 then (a F).1 else 0) -
      (∑ F ∈ pairSet H, if Disjoint F S.1 then (a F).2 else 0)) / (36 : K) +
    (19 / 12 : K) * (∑ F ∈ pairSet H, (a F).1)

/-- Combined side readout: pair correction followed by the direct diagonal add. -/
def aggregateRead (a : AggregateBank K) : Source → K :=
  fun S => pairRead a.1 S + a.2 S

noncomputable def aggregateReadHom : AggregateBank K →+ (Source → K) where
  toFun := aggregateRead
  map_zero' := by
    funext S
    simp [aggregateRead, pairRead]
  map_add' := by
    intro a b
    funext S
    simp only [aggregateRead, pairRead, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    have hsub :
        (∑ F ∈ pairSet H, if F ⊆ S.1 then (a.1 F).1 + (b.1 F).1 else 0) =
          (∑ F ∈ pairSet H, if F ⊆ S.1 then (a.1 F).1 else 0) +
            ∑ F ∈ pairSet H, if F ⊆ S.1 then (b.1 F).1 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases h : F ⊆ S.1 <;> simp [h]
    have hdis :
        (∑ F ∈ pairSet H, if Disjoint F S.1 then (a.1 F).2 + (b.1 F).2 else 0) =
          (∑ F ∈ pairSet H, if Disjoint F S.1 then (a.1 F).2 else 0) +
            ∑ F ∈ pairSet H, if Disjoint F S.1 then (b.1 F).2 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases h : Disjoint F S.1 <;> simp [h]
    have hall :
        (∑ F ∈ pairSet H, ((a.1 F).1 + (b.1 F).1)) =
          (∑ F ∈ pairSet H, (a.1 F).1) +
            ∑ F ∈ pairSet H, (b.1 F).1 := by
      rw [Finset.sum_add_distrib]
    rw [hsub, hdis, hall]
    ring

theorem pairAggregates_add (x y : Source → K) :
    pairAggregates (x + y) = pairAggregates x + pairAggregates y := by
  funext F
  apply Prod.ext
  · simp only [pairAggregates, Pi.add_apply, Prod.add_def]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hF : F ⊆ T.1 <;> simp [hF]
  · simp only [pairAggregates, Pi.add_apply, Prod.add_def]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hF : Disjoint F T.1 <;> simp [hF]

private theorem pairRead_pairAggregates (x : Source → K) (S : Source) :
    pairRead (pairAggregates x) S =
      ∑ T ∈ (tripleSet H).attach,
        ((1 - ((S.1 ∩ T.1).card : K)) / 2) * x T := by
  classical
  unfold pairRead pairAggregates
  simp only [Prod.fst, Prod.snd]
  have hA :
      (∑ F ∈ pairSet H, if F ⊆ S.1 then
        (∑ T ∈ (tripleSet H).attach, if F ⊆ T.1 then x T else 0) else 0) =
      ∑ T ∈ (tripleSet H).attach,
        (((S.1 ∩ T.1).card.choose 2 : K) * x T) := by
    calc
      (∑ F ∈ pairSet H, if F ⊆ S.1 then
          (∑ T ∈ (tripleSet H).attach, if F ⊆ T.1 then x T else 0) else 0) =
          ∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
            if F ⊆ S.1 then (if F ⊆ T.1 then x T else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro F hF
              by_cases hS : F ⊆ S.1 <;> simp [hS]
      _ = ∑ T ∈ (tripleSet H).attach, ∑ F ∈ pairSet H,
            if F ⊆ S.1 then (if F ⊆ T.1 then x T else 0) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ T ∈ (tripleSet H).attach,
            (((S.1 ∩ T.1).card.choose 2 : K) * x T) := by
              apply Finset.sum_congr rfl
              intro T hT
              exact sum_pair_both S T (x T)
  have hB :
      (∑ F ∈ pairSet H, if Disjoint F S.1 then
        (∑ T ∈ (tripleSet H).attach, if Disjoint F T.1 then x T else 0) else 0) =
      ∑ T ∈ (tripleSet H).attach,
        (((Finset.univ : Finset (Fin H)).card - (S.1 ∪ T.1).card).choose 2 : K) * x T := by
    calc
      (∑ F ∈ pairSet H, if Disjoint F S.1 then
          (∑ T ∈ (tripleSet H).attach, if Disjoint F T.1 then x T else 0) else 0) =
          ∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
            if Disjoint F S.1 then (if Disjoint F T.1 then x T else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro F hF
              by_cases hS : Disjoint F S.1 <;> simp [hS]
      _ = ∑ T ∈ (tripleSet H).attach, ∑ F ∈ pairSet H,
            if Disjoint F S.1 then (if Disjoint F T.1 then x T else 0) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ T ∈ (tripleSet H).attach,
            (((Finset.univ : Finset (Fin H)).card - (S.1 ∪ T.1).card).choose 2 : K) * x T := by
              apply Finset.sum_congr rfl
              intro T hT
              exact sum_pair_disjoint S T (x T)
  have hGlobal :
      (∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
        if F ⊆ T.1 then x T else 0) =
      ∑ T ∈ (tripleSet H).attach, (3 : K) * x T := by
    calc
      (∑ F ∈ pairSet H, ∑ T ∈ (tripleSet H).attach,
          if F ⊆ T.1 then x T else 0) =
          ∑ T ∈ (tripleSet H).attach, ∑ F ∈ pairSet H,
            if F ⊆ T.1 then x T else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ T ∈ (tripleSet H).attach, (3 : K) * x T := by
            apply Finset.sum_congr rfl
            intro T hT
            calc
              (∑ F ∈ pairSet H, if F ⊆ T.1 then x T else 0) =
                  ∑ F ∈ pairSet H,
                    (if F ⊆ T.1 then (if F ⊆ T.1 then x T else 0) else 0) := by
                      apply Finset.sum_congr rfl
                      intro F hF
                      by_cases hFT : F ⊆ T.1 <;> simp [hFT]
              _ = ((T.1 ∩ T.1).card.choose 2 : K) * x T :=
                    sum_pair_both T T (x T)
              _ = (3 : K) * x T := by
                    simp [triple_card T]
  have hU (T : Source) : (S.1 ∪ T.1).card = 6 - (S.1 ∩ T.1).card := by
    have hu := Finset.card_union_add_card_inter S.1 T.1
    rw [triple_card S, triple_card T] at hu
    omega
  rw [hA, hB, hGlobal]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp_rw [hU]
  rw [← Finset.sum_sub_distrib]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  -- The remaining arithmetic is the four possible intersection cardinalities.
  apply Finset.sum_congr rfl
  intro T hT
  by_cases heq : S = T
  · subst T
    simp [triple_card S]
    norm_num [Nat.choose] <;> ring
  · have hlt := inter_card_lt_three S T heq
    have hle : (S.1 ∩ T.1).card ≤ 3 := le_trans (Nat.le_of_lt_succ hlt) (by omega)
    interval_cases hr : (S.1 ∩ T.1).card <;>
      simp [hr, heq] <;> norm_num [Nat.choose] <;> ring

/-- Scalar identity for the pair/complement route, with the direct diagonal bank. -/
theorem identity (x : Source → K) :
    CompressedInvocation.OrderedPairs.RHom
          (CenterCompression.compressedG x) +
        aggregateReadHom (aggregateInput x) = x := by
  funext S
  change compressedR S (compressedG x) +
      (pairRead (pairAggregates x) S + x S) = x S
  rw [pairRead_pairAggregates]
  have hRG :
      compressedR S (compressedG x) =
        ∑ T ∈ (tripleSet H).attach,
          (((S.1 ∩ T.1).card : K) - 1) / 2 * x T := by
    rw [compressed_RG]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  rw [hRG]
  have hpoint (T : Source) :
      (((S.1 ∩ T.1).card : K) - 1) / 2 * x T +
        (1 - ((S.1 ∩ T.1).card : K)) / 2 * x T = 0 := by
    ring
  have hzero :
      Finset.sum ((tripleSet H).attach)
        (fun T =>
          (((S.1 ∩ T.1).card : K) - 1) / 2 * x T +
            (1 - ((S.1 ∩ T.1).card : K)) / 2 * x T) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    exact hpoint T
  have hsum :
      Finset.sum ((tripleSet H).attach)
          (fun T => (((S.1 ∩ T.1).card : K) - 1) / 2 * x T) +
        Finset.sum ((tripleSet H).attach)
          (fun T => (1 - ((S.1 ∩ T.1).card : K)) / 2 * x T) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact hzero
  calc
    _ = (Finset.sum ((tripleSet H).attach) (fun T =>
          (((S.1 ∩ T.1).card : K) - 1) / 2 * x T) +
        Finset.sum ((tripleSet H).attach) (fun T =>
          (1 - ((S.1 ∩ T.1).card : K)) / 2 * x T)) + x S := by
            ring
    _ = x S := by
              rw [hsum]
              ring

/-- Forward eight-row invocation restores arbitrary pair and diagonal banks. -/
theorem forward_restore
    (s : CompressedInvocation.State (Source → K) (AggregateBank K) (Fin H → K)) :
    CompressedInvocation.eightRows
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        aggregateReadHom
        aggregateInput s = {s with y := s.y + s.x} := by
  exact @CompressedInvocation.eightRows_restore (Source → K) (AggregateBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom CenterCompression.compressedG
    aggregateReadHom aggregateInput identity s

/-- Inverse eight-row invocation restores arbitrary pair and diagonal banks. -/
theorem inverse_restore
    (s : CompressedInvocation.State (Source → K) (AggregateBank K) (Fin H → K)) :
    CompressedInvocation.inverseEightRows
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        aggregateReadHom
        aggregateInput s = {s with y := s.y - s.x} := by
  exact @CompressedInvocation.inverseEightRows_restore (Source → K) (AggregateBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom CenterCompression.compressedG
    aggregateReadHom aggregateInput identity s

/-- Three scalar invocations exchange the logical source and target banks. -/
theorem three_exchange
    (s : CompressedInvocation.State (Source → K) (AggregateBank K) (Fin H → K)) :
    CompressedInvocation.threeInvocations
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        aggregateReadHom
        aggregateInput s = {s with x := -s.y, y := s.x} := by
  exact @CompressedInvocation.threeInvocations_exchange (Source → K) (AggregateBank K)
    (Fin H → K) _ _ _
    CompressedInvocation.OrderedPairs.RHom CenterCompression.compressedG
    aggregateReadHom aggregateInput identity s

end H24
end PairComplementInvocation
end ExactFourier
end OAI
