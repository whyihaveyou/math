import OAI.Computability.FourierCircuit.FrameLabels
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Pure-tensor frame labels

The paper's binary address space is a triple tensor power.  We represent that
space concretely as functions on `Fin h × (Fin h × Fin h)` and prove the
factorisation of the standard dot product on pure indicator tensors.  This
discharges the local unit-norm and neighbour-orthogonality facts for the
one-dimensional labels `U_d`; the remaining stage labels are tensor products
with complements and are still a separate development.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace TensorFrameLabels

open FrameLabels

def tensor3 {h : ℕ} (A B C : Finset (Fin h)) :
    Fin h × (Fin h × Fin h) → ZMod 2 :=
  fun x => indicator A x.1 * indicator B x.2.1 * indicator C x.2.2

def pure3 {h : ℕ} (a b c : Fin h → ZMod 2) :
    Fin h × (Fin h × Fin h) → ZMod 2 :=
  fun x => a x.1 * b x.2.1 * c x.2.2

theorem pure3_dot
    {h : ℕ} (a b c a' b' c' : Fin h → ZMod 2) :
    dotProduct (pure3 a b c) (pure3 a' b' c') =
      dotProduct a a' * dotProduct b b' * dotProduct c c' := by
  classical
  change (∑ x : Fin h × (Fin h × Fin h),
      pure3 a b c x * pure3 a' b' c' x) =
    (∑ i : Fin h, a i * a' i) *
      (∑ j : Fin h, b j * b' j) *
        (∑ k : Fin h, c k * c' k)
  simp only [pure3]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  let K : ZMod 2 := ∑ k, c k * c' k
  have hinner : ∀ i j, (∑ k,
      a i * b j * c k * (a' i * b' j * c' k)) =
      (a i * a' i) * ((b j * b' j) * K) := by
    intro i j
    calc
      (∑ k, a i * b j * c k * (a' i * b' j * c' k)) =
          ∑ k, (a i * a' i) *
            ((b j * b' j) * (c k * c' k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (a i * a' i) * ((b j * b' j) * K) := by
            calc
              (∑ k, (a i * a' i) *
                  ((b j * b' j) * (c k * c' k))) =
                  (a i * a' i) *
                    (∑ k, (b j * b' j) * (c k * c' k)) := by
                symm
                simpa [mul_assoc] using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin h)))
                    (fun k => (b j * b' j) * (c k * c' k))
                    (a i * a' i))
              _ = (a i * a' i) * ((b j * b' j) * K) := by
                congr 1
                symm
                simpa [K] using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin h)))
                    (fun k => c k * c' k) (b j * b' j))
  simp_rw [hinner]
  calc
    (∑ i, ∑ j, (a i * a' i) * ((b j * b' j) * K)) =
        (∑ i, a i * a' i) *
          (∑ j, (b j * b' j) * K) := by
      symm
      exact Fintype.sum_mul_sum (fun i => a i * a' i)
        (fun j => (b j * b' j) * K)
    _ = (∑ i, a i * a' i) *
        ((∑ j, b j * b' j) * K) := by
      congr 1
      rw [← Finset.sum_mul]
    _ = (∑ i, a i * a' i) *
        (∑ j, b j * b' j) *
        (∑ k, c k * c' k) := by
      simp [K, mul_assoc]

theorem pure3_norm_of_unit
    {h : ℕ} (a b c : Fin h → ZMod 2)
    (ha : dotProduct a a = 1) (hb : dotProduct b b = 1)
    (hc : dotProduct c c = 1) :
    dotProduct (pure3 a b c) (pure3 a b c) = (1 : ZMod 2) := by
  rw [pure3_dot, ha, hb, hc]
  decide

theorem pure3_orthogonal_of_first
    {h : ℕ} (a b c a' b' c' : Fin h → ZMod 2)
    (ha : dotProduct a a' = 0) :
    dotProduct (pure3 a b c) (pure3 a' b' c') = 0 := by
  rw [pure3_dot, ha]
  simp

def tensorDotForm {h : ℕ} :
    (Fin h × (Fin h × Fin h) → ZMod 2) →ₗ[ZMod 2]
      (Fin h × (Fin h × Fin h) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun v w => dotProduct v w)
    (by intro v₁ v₂ w; simp [dotProduct, Finset.sum_add_distrib, add_mul])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_assoc])
    (by intro v w₁ w₂; simp [dotProduct, Finset.sum_add_distrib, mul_add])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_left_comm])

theorem tensor3_dot
    {h : ℕ} (A B C A' B' C' : Finset (Fin h)) :
    dotProduct (tensor3 A B C) (tensor3 A' B' C') =
      dotForm (indicator A) (indicator A') *
        dotForm (indicator B) (indicator B') *
          dotForm (indicator C) (indicator C') := by
  classical
  change (∑ x : Fin h × (Fin h × Fin h),
      tensor3 A B C x * tensor3 A' B' C' x) =
    (∑ i : Fin h, indicator A i * indicator A' i) *
      (∑ j : Fin h, indicator B j * indicator B' j) *
        (∑ k : Fin h, indicator C k * indicator C' k)
  simp only [tensor3]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  let K : ZMod 2 := ∑ k, indicator C k * indicator C' k
  have hinner : ∀ i j, (∑ k,
      indicator A i * indicator B j * indicator C k *
        (indicator A' i * indicator B' j * indicator C' k)) =
      (indicator A i * indicator A' i) *
        ((indicator B j * indicator B' j) * K) := by
    intro i j
    calc
      (∑ k, indicator A i * indicator B j * indicator C k *
          (indicator A' i * indicator B' j * indicator C' k)) =
          ∑ k, (indicator A i * indicator A' i) *
            ((indicator B j * indicator B' j) *
              (indicator C k * indicator C' k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (indicator A i * indicator A' i) *
          ((indicator B j * indicator B' j) * K) := by
            calc
              (∑ k, (indicator A i * indicator A' i) *
                  ((indicator B j * indicator B' j) *
                    (indicator C k * indicator C' k))) =
                  (indicator A i * indicator A' i) *
                    (∑ k, (indicator B j * indicator B' j) *
                      (indicator C k * indicator C' k)) := by
                symm
                simpa [mul_assoc] using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin h)))
                    (fun k => (indicator B j * indicator B' j) *
                      (indicator C k * indicator C' k))
                    (indicator A i * indicator A' i))
              _ = (indicator A i * indicator A' i) *
                  ((indicator B j * indicator B' j) * K) := by
                congr 1
                symm
                simpa [K] using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin h)))
                    (fun k => indicator C k * indicator C' k)
                    (indicator B j * indicator B' j))
  simp_rw [hinner]
  calc
    (∑ x, ∑ x_1, (indicator A x * indicator A' x) *
        ((indicator B x_1 * indicator B' x_1) * K)) =
        (∑ x, indicator A x * indicator A' x) *
          (∑ x_1, (indicator B x_1 * indicator B' x_1) * K) := by
      symm
      exact Fintype.sum_mul_sum (fun x => indicator A x * indicator A' x)
        (fun x_1 => (indicator B x_1 * indicator B' x_1) * K)
    _ = (∑ x, indicator A x * indicator A' x) *
        ((∑ x_1, indicator B x_1 * indicator B' x_1) * K) := by
      congr 1
      rw [← Finset.sum_mul]
    _ = (∑ x, indicator A x * indicator A' x) *
        (∑ x_1, indicator B x_1 * indicator B' x_1) *
        (∑ k, indicator C k * indicator C' k) := by
      simp [K, mul_assoc]

theorem tensor3_dotForm_apply {h : ℕ}
    (v w : Fin h × (Fin h × Fin h) → ZMod 2) :
    tensorDotForm v w = dotProduct v w := rfl

theorem tensor3_norm_of_triples {h : ℕ}
    (A B C : Finset (Fin h))
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) :
    tensorDotForm (tensor3 A B C) (tensor3 A B C) = (1 : ZMod 2) := by
  change dotProduct (tensor3 A B C) (tensor3 A B C) = (1 : ZMod 2)
  rw [tensor3_dot]
  rw [indicator_triple_norm A hA, indicator_triple_norm B hB,
    indicator_triple_norm C hC]
  decide

theorem tensor3_orthogonal_of_even {h : ℕ}
    (A B C A' B' C' : Finset (Fin h))
    (heven : Even (A ∩ A').card) :
    tensorDotForm (tensor3 A B C) (tensor3 A' B' C') = 0 := by
  change dotProduct (tensor3 A B C) (tensor3 A' B' C') = 0
  rw [tensor3_dot]
  have heven' : Even (A' ∩ A).card := by
    simpa [Finset.inter_comm] using heven
  rw [indicator_orthogonal_of_even A' A heven']
  simp

theorem tensor3_line_is_complement {h : ℕ}
    (A B C : Finset (Fin h))
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3) :
    IsCompl ((ZMod 2) ∙ tensor3 A B C)
      (((ZMod 2) ∙ tensor3 A B C).orthogonalBilin (tensorDotForm : _)) := by
  have hnorm : tensorDotForm (tensor3 A B C) (tensor3 A B C) ≠ 0 := by
    rw [tensor3_norm_of_triples A B C hA hB hC]
    decide
  exact LinearMap.isCompl_span_singleton_orthogonal hnorm

theorem tensor3_neighbour_line_nested {h : ℕ}
    (A B C A' B' C' : Finset (Fin h))
    (heven : Even (A ∩ A').card) :
    (ZMod 2) ∙ tensor3 A B C ≤
      ((ZMod 2) ∙ tensor3 A' B' C').orthogonalBilin (tensorDotForm : _) := by
  apply line_in_orthogonal_line tensorDotForm
  change dotProduct (tensor3 A' B' C') (tensor3 A B C) = 0
  rw [tensor3_dot]
  rw [indicator_orthogonal_of_even A A']
  · simp
  · simpa [Finset.inter_comm] using heven

end TensorFrameLabels
end ExactFourier
end OAI
