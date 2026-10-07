import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Complement-moment query tradeoff

For a family of singleton incidence moments `a_i`, set
`b_i = A - 3 a_i`, where `A = sum_i a_i`.  The `b_i` basis is the natural
weighted cancellation whose source support consists of triples avoiding `i`.
The two identities below isolate its scalar tradeoff: a target triple can be
recovered from three `b_i` entries only after the global total `A` is known,
and `A` itself is obtained from the sum of all `b_i` with a dense read.

This is an exact scalar statement.  It makes no frame or complexity claim.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace ComplementMomentTradeoff

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [CharZero K]

def total (a : ι → K) : K := ∑ i, a i

def complement (a : ι → K) (i : ι) : K := total a - 3 * a i

omit [DecidableEq ι] [CharZero K] in
theorem complement_entry (a : ι → K) (i : ι) :
    total a - complement a i = 3 * a i := by
  unfold complement
  ring

omit [DecidableEq ι] in
theorem complement_query {S : Finset ι} (a : ι → K)
    (hS : S.card = 3) :
    (∑ i ∈ S, (total a - complement a i)) / 3 = ∑ i ∈ S, a i := by
  rw [Finset.sum_sub_distrib]
  have htotal : (∑ _i ∈ S, total a) = 3 * total a := by
    rw [Finset.sum_const, hS]
    norm_num
  have hcomp : (∑ i ∈ S, complement a i) =
      3 * total a - 3 * (∑ i ∈ S, a i) := by
    unfold complement
    rw [Finset.sum_sub_distrib]
    rw [htotal]
    rw [← Finset.mul_sum]
  rw [htotal, hcomp]
  field_simp
  ring

omit [DecidableEq ι] [CharZero K] in
theorem complement_total
    (a : ι → K) (hι : (Fintype.card ι : K) - 3 ≠ 0) :
    total a = (∑ i, complement a i) / ((Fintype.card ι : K) - 3) := by
  unfold complement total
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  field_simp

end ComplementMomentTradeoff
end ExactFourier
end OAI
