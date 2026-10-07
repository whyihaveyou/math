import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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

end CenterCompression
end ExactFourier
end OAI
