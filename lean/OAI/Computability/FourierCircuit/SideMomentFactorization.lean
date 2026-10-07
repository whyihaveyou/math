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

/- The same correction with its diagonal term removed.  The missing `x S`
   is then supplied by a direct source-to-target bank shear. -/
def sideMomentNoDiag {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (x : Triple h → K) : K :=
  (sideMoment0 x - ∑ i ∈ S.1, sideMoment1 x i) / 2

theorem sideMomentAction_eq_noDiag_add
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    sideMomentAction S x = sideMomentNoDiag S x + x S := by
  unfold sideMomentAction sideMomentNoDiag
  ring

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


def sideRead {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (a0 : K) (a1 : Fin h → K) : K :=
  (a0 - ∑ i ∈ S.1, a1 i) / 2

def centerRead {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (c : Fin h → K) : K :=
  (∑ i ∈ S.1, c i) / 2

theorem sideRead_update
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) (a0 : K) (a1 : Fin h → K) :
    sideRead S (a0 + sideMoment0 x)
      (fun i => a1 i + sideMoment1 x i) =
      sideRead S a0 a1 +
        (sideMoment0 x - ∑ i ∈ S.1, sideMoment1 x i) / 2 := by
  unfold sideRead
  rw [Finset.sum_add_distrib]
  ring

theorem centerRead_update
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) (c : Fin h → K) :
    centerRead S (fun i => c i + compressedG (K := K) x i) =
      centerRead S c + compressedR S (compressedG (K := K) x) := by
  unfold centerRead compressedR
  rw [Finset.sum_add_distrib]
  ring

theorem invocation_identity
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x y : Triple h → K)
    (a0 : K) (a1 : Fin h → K) (c : Fin h → K) :
    (y S - sideRead S a0 a1 - centerRead S c) +
        sideRead S (a0 + sideMoment0 x)
          (fun i => a1 i + sideMoment1 x i) +
        centerRead S (fun i => c i + compressedG (K := K) x i) + x S =
      y S + x S := by
  rw [sideRead_update, centerRead_update]
  have hmoment :
      (sideMoment0 x - ∑ i ∈ S.1, sideMoment1 x i) / 2 + x S =
        sideMomentAction S x := by
    unfold sideMomentAction
    ring
  calc
    y S - sideRead S a0 a1 - centerRead S c +
          (sideRead S a0 a1 + (sideMoment0 x -
            ∑ i ∈ S.1, sideMoment1 x i) / 2) +
          (centerRead S c + compressedR S (compressedG (K := K) x)) + x S =
        y S + compressedR S (compressedG (K := K) x) +
          ((sideMoment0 x - ∑ i ∈ S.1, sideMoment1 x i) / 2 + x S) := by ring
    _ = y S + compressedR S (compressedG (K := K) x) + sideMomentAction S x := by
      rw [hmoment]
    _ = y S + (compressedR S (compressedG (K := K) x) + sideMomentAction S x) := by ring
    _ = y S + x S := by
      rw [compressed_plus_moment_side]

/- The diagonal-free moment correction cancels the compressed centre map.
   This is the algebraic form behind a possible direct bank shear. -/
theorem compressed_plus_moment_noDiag
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + sideMomentNoDiag S x = 0 := by
  calc
    compressedR S (compressedG (K := K) x) + sideMomentNoDiag S x =
        (compressedR S (compressedG (K := K) x) + sideMomentAction S x) - x S := by
          rw [sideMomentAction_eq_noDiag_add]
          ring
    _ = x S - x S := by rw [compressed_plus_moment_side]
    _ = 0 := sub_self _

theorem compressed_plus_moment_noDiag_direct
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + sideMomentNoDiag S x + x S = x S := by
  rw [compressed_plus_moment_noDiag]
  ring


end SideMomentFactorization
end ExactFourier
end OAI
