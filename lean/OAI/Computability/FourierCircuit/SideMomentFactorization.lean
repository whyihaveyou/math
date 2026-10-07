import OAI.Computability.FourierCircuit.CenterMap
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

open scoped BigOperators
namespace OAI
namespace ExactFourier
namespace SideMomentFactorization

open CenterCompression

def sideMoment0 {h : ℕ} {K : Type*} [Field K]
    (x : Triple h → K) : K :=
  ∑ T ∈ (tripleSet h).attach, x T

def sideMoment1 {h : ℕ} {K : Type*} [Field K]
    (x : Triple h → K) (i : Fin h) : K :=
  ∑ T ∈ (tripleSet h).attach, if i ∈ T.1 then x T else 0

def sideMomentAction {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (x : Triple h → K) : K :=
  (sideMoment0 x - ∑ i ∈ S.1, sideMoment1 x i + 2 * x S) / 2

theorem incidence_weighted
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    (∑ i ∈ S.1, ∑ T ∈ (tripleSet h).attach,
      if i ∈ T.1 then x T else 0) =
      ∑ T ∈ (tripleSet h).attach,
        ((S.1 ∩ T.1).card : K) * x T := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    (∑ x_1 ∈ S.1, if x_1 ∈ T.1 then x T else 0) =
        (∑ x_1 ∈ S.1, (if x_1 ∈ T.1 then (1 : K) else 0)) * x T := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hit : i ∈ T.1 <;> simp [hit]
    _ = ((S.1 ∩ T.1).card : K) * x T := by
          rw [incidence_sum]

theorem compressed_plus_moment_side
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + sideMomentAction S x = x S := by
  classical
  rw [compressed_RG]
  unfold sideMomentAction sideMoment0 sideMoment1
  have hweighted :
      (∑ i ∈ S.1, ∑ T ∈ (tripleSet h).attach,
        if i ∈ T.1 then x T else 0) =
        ∑ T ∈ (tripleSet h).attach,
          ((S.1 ∩ T.1).card : K) * x T := incidence_weighted S x
  rw [hweighted]
  have hB :
      (∑ T ∈ (tripleSet h).attach, x T) =
        ∑ T ∈ (tripleSet h).attach, (1 : K) * x T := by
    apply Finset.sum_congr rfl
    intro T hT
    simp
  have hzero :
      (∑ T ∈ (tripleSet h).attach,
          (((S.1 ∩ T.1).card : K) - 1) * x T) -
        ∑ T ∈ (tripleSet h).attach,
          ((S.1 ∩ T.1).card : K) * x T +
            ∑ T ∈ (tripleSet h).attach, x T = 0 := by
    rw [hB]
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro T hT
    ring
  field_simp
  calc
    (∑ T ∈ (tripleSet h).attach,
        (((S.1 ∩ T.1).card : K) - 1) * x T) +
        ((∑ T ∈ (tripleSet h).attach, x T) -
          ∑ T ∈ (tripleSet h).attach,
            ((S.1 ∩ T.1).card : K) * x T + 2 * x S) =
        ((∑ T ∈ (tripleSet h).attach,
          (((S.1 ∩ T.1).card : K) - 1) * x T) -
          ∑ T ∈ (tripleSet h).attach,
            ((S.1 ∩ T.1).card : K) * x T +
            ∑ T ∈ (tripleSet h).attach, x T) + 2 * x S := by ring
    _ = 2 * x S := by rw [hzero]; ring

end SideMomentFactorization
end ExactFourier
end OAI
