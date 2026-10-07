import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import OAI.Computability.FourierCircuit.CenterCompression

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterCompression

def tripleSet (h : ℕ) : Finset (Finset (Fin h)) :=
  (Finset.univ : Finset (Fin h)).powerset.filter (fun T => T.card = 3)

abbrev Triple (h : ℕ) := {T : Finset (Fin h) // T ∈ tripleSet h}

def compressedG {h : ℕ} {K : Type*} [Field K]
    (x : Triple h → K) : Fin h → K :=
  fun i => (∑ T ∈ (tripleSet h).attach,
      if i ∈ T.1 then x T else 0) -
    (∑ T ∈ (tripleSet h).attach, x T) / (3 : K)

def compressedR {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (c : Fin h → K) : K :=
  (∑ i ∈ S.1, c i) / (2 : K)

theorem triple_card {h : ℕ} (S : Triple h) : S.1.card = 3 := by
  exact (Finset.mem_filter.mp (show S.1 ∈ (Finset.univ : Finset (Fin h)).powerset.filter (fun T => T.card = 3) from S.2)).2

theorem compressed_RG_basis
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S T : Triple h) :
    compressedR S (compressedG (K := K) (fun U => if U = T then 1 else 0)) =
      ((S.1 ∩ T.1).card - 1 : K) / 2 := by
  classical
  unfold compressedR compressedG
  rw [Finset.sum_sub_distrib]
  have hinc : ∀ i : Fin h,
      (∑ U ∈ (tripleSet h).attach,
          if i ∈ U.1 then (if U = T then (1 : K) else 0) else 0) =
        if i ∈ T.1 then (1 : K) else 0 := by
    intro i
    have hs := Finset.sum_eq_single (s := (tripleSet h).attach) T
      (f := fun U : Triple h =>
        if i ∈ U.1 then (if U = T then (1 : K) else 0) else 0)
      (by
        intro U hU hne
        simp [hne])
      (by
        intro hnot
        exact False.elim (hnot (Finset.mem_attach _ T)))
    simpa using hs
  have hsum : (∑ U ∈ (tripleSet h).attach,
      (if U = T then (1 : K) else 0)) = 1 := by
    have hs := Finset.sum_eq_single (s := (tripleSet h).attach) T
      (f := fun U : Triple h => if U = T then (1 : K) else 0)
      (by
        intro U hU hne
        simp [hne])
      (by
        intro hnot
        exact False.elim (hnot (Finset.mem_attach _ T)))
    simpa only [ite_eq_left rfl, ite_true] using hs
  simp_rw [hinc]
  rw [hsum]
  rw [← Finset.sum_sub_distrib]
  exact compressed_triple_entry S.1 T.1 (triple_card S)


theorem compressed_RG
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) =
      (∑ T ∈ (tripleSet h).attach,
        (((S.1 ∩ T.1).card : K) - 1) * x T) / 2 := by
  classical
  unfold compressedR compressedG
  rw [Finset.sum_sub_distrib]
  have hinner : ∀ T : Triple h,
      (∑ i ∈ S.1, if i ∈ T.1 then x T else 0) =
        ((S.1 ∩ T.1).card : K) * x T := by
    intro T
    calc
      (∑ i ∈ S.1, if i ∈ T.1 then x T else 0) =
          (∑ i ∈ S.1, (if i ∈ T.1 then (1 : K) else 0) * x T) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hit : i ∈ T.1 <;> simp [hit]
      _ = (∑ i ∈ S.1, (if i ∈ T.1 then (1 : K) else 0)) * x T := by
            rw [Finset.sum_mul]
      _ = ((S.1 ∩ T.1).card : K) * x T := by
            rw [incidence_sum]
  have hswap :
      (∑ i ∈ S.1, ∑ T ∈ (tripleSet h).attach,
        if i ∈ T.1 then x T else 0) =
        ∑ T ∈ (tripleSet h).attach, ∑ i ∈ S.1,
          if i ∈ T.1 then x T else 0 := by
    rw [Finset.sum_comm]
  have hcentre :
      (∑ i ∈ S.1, (∑ T ∈ (tripleSet h).attach, x T) / (3 : K)) =
        ∑ T ∈ (tripleSet h).attach, x T := by
    calc
      (∑ i ∈ S.1, (∑ T ∈ (tripleSet h).attach, x T) / (3 : K)) =
          (∑ i ∈ S.1, (1 : K)) *
            ((∑ T ∈ (tripleSet h).attach, x T) / (3 : K)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              simp
      _ = (3 : K) *
            ((∑ T ∈ (tripleSet h).attach, x T) / (3 : K)) := by
              rw [Finset.sum_const, triple_card S]
              norm_num
      _ = ∑ T ∈ (tripleSet h).attach, x T := by
              field_simp
  rw [hswap]
  simp_rw [hinner]
  rw [hcentre]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (fun z => z / 2)
  apply Finset.sum_congr rfl
  intro T hT
  ring

def sideCoeff {h : ℕ} {K : Type*} [Field K]
    (S T : Triple h) : K :=
  if S = T then 0 else if Even (S.1 ∩ T.1).card then
    -(((S.1 ∩ T.1).card : K) - 1) / 2 else 0

theorem inter_card_lt_three {h : ℕ} (S T : Triple h) (hne : S ≠ T) :
    (S.1 ∩ T.1).card < 3 := by
  have hle : (S.1 ∩ T.1).card ≤ S.1.card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [triple_card S] at hle
  by_contra hnot
  have heqcard : (S.1 ∩ T.1).card = 3 := by omega
  have hIS : S.1 ∩ T.1 = S.1 := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    simpa [heqcard, triple_card S]
  have hST : S.1 ⊆ T.1 := by
    intro i hi
    have hi' : i ∈ S.1 ∩ T.1 := by
      rw [hIS]
      exact hi
    exact (Finset.mem_inter.mp hi').2
  have hEq : S.1 = T.1 := by
    apply Finset.eq_of_subset_of_card_le hST
    rw [triple_card T, triple_card S]
  exact hne (Subtype.ext hEq)

theorem inter_card_eq_one_of_not_even {h : ℕ} (S T : Triple h) (hne : S ≠ T)
    (hnot : ¬ Even (S.1 ∩ T.1).card) : (S.1 ∩ T.1).card = 1 := by
  have hlt := inter_card_lt_three S T hne
  have hodd : Odd (S.1 ∩ T.1).card := Nat.not_even_iff_odd.mp hnot
  rcases hodd with ⟨k, hk⟩
  omega

theorem coefficient_plus_side_basis
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S T : Triple h) :
    (((S.1 ∩ T.1).card : K) - 1) / 2 + sideCoeff S T =
      if S = T then (1 : K) else 0 := by
  by_cases hST : S = T
  · subst T
    simp [sideCoeff, triple_card S]
    norm_num
  · by_cases heven : Even (S.1 ∩ T.1).card
    · simp [sideCoeff, hST, heven]
      ring
    · have hone := inter_card_eq_one_of_not_even S T hST heven
      simp [sideCoeff, hST, hone]

theorem compressed_plus_side_basis
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S T : Triple h) :
    compressedR S (compressedG (K := K) (fun U => if U = T then 1 else 0)) +
      sideCoeff S T = if S = T then (1 : K) else 0 := by
  rw [compressed_RG_basis]
  exact coefficient_plus_side_basis S T



def sideAction {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (x : Triple h → K) : K :=
  ∑ T ∈ (tripleSet h).attach, sideCoeff S T * x T

theorem compressed_plus_side
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + sideAction S x = x S := by
  classical
  rw [compressed_RG]
  have hdiv :
      (∑ T ∈ (tripleSet h).attach,
        (((S.1 ∩ T.1).card : K) - 1) * x T) / 2 =
        ∑ T ∈ (tripleSet h).attach,
          ((((S.1 ∩ T.1).card : K) - 1) / 2) * x T := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  rw [hdiv, sideAction, ← Finset.sum_add_distrib]
  have hs := Finset.sum_eq_single (s := (tripleSet h).attach) S
    (f := fun T : Triple h =>
      (if S = T then (1 : K) else 0) * x T)
    (by
      intro T hT hne
      simp [Ne.symm hne])
    (by
      intro hnot
      exact False.elim (hnot (Finset.mem_attach _ S)))
  have hcoeff : ∀ T : Triple h,
      ((((S.1 ∩ T.1).card : K) - 1) / 2) * x T + sideCoeff S T * x T =
        (if S = T then (1 : K) else 0) * x T := by
    intro T
    rw [← add_mul, coefficient_plus_side_basis]
  simp_rw [hcoeff]
  simpa only [ite_true, one_mul] using hs

end CenterCompression
end ExactFourier
end OAI
