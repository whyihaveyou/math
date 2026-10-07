import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Small binary-frame lemmas used by the side-wire audit

The paper labels a triple by its indicator vector over `F₂`.  This file checks
the two local facts needed for the neighbour side edge: indicator dot products
are intersection parities, and an even-intersection pair gives a nested line
inside an orthogonal complement.  It also records the unit-norm fact for a
three-element triple.  Tensor-product labels and the full eight-row network
remain outside this small certificate.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace FrameLabels

def indicator {h : ℕ} (T : Finset (Fin h)) : Fin h → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

def dotForm {h : ℕ} :
    (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun v w => dotProduct v w)
    (by intro v₁ v₂ w; simp [dotProduct, Finset.sum_add_distrib, add_mul])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_assoc])
    (by intro v w₁ w₂; simp [dotProduct, Finset.sum_add_distrib, mul_add])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_left_comm])

theorem indicator_dot {h : ℕ} (S T : Finset (Fin h)) :
    dotForm (indicator S) (indicator T) = ((S ∩ T).card : ZMod 2) := by
  simp [dotForm, indicator, dotProduct]
  rw [Finset.inter_comm]

theorem indicator_triple_norm {h : ℕ} (S : Finset (Fin h)) (hS : S.card = 3) :
    dotForm (indicator S) (indicator S) = (1 : ZMod 2) := by
  rw [indicator_dot]
  simp only [Finset.inter_self, hS]
  decide

theorem indicator_orthogonal_of_even {h : ℕ} (S T : Finset (Fin h))
    (heven : Even (S ∩ T).card) :
    dotForm (indicator T) (indicator S) = 0 := by
  rw [indicator_dot]
  rw [Finset.inter_comm]
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  rw [Nat.cast_add]
  have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  calc
    (k : ZMod 2) + k = (2 : ZMod 2) * k := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem line_in_orthogonal_line
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : V →ₗ[K] V →ₗ[K] K) (x y : V) (h : B y x = 0) :
    K ∙ x ≤ (K ∙ y).orthogonalBilin B := by
  rw [Submodule.orthogonalBilin_span_singleton]
  intro z hz
  rw [LinearMap.mem_ker]
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h]

theorem neighboring_line_nested {h : ℕ} (S T : Finset (Fin h))
    (heven : Even (S ∩ T).card) :
    (ZMod 2) ∙ indicator S ≤
      ((ZMod 2) ∙ indicator T).orthogonalBilin (dotForm : _ ) := by
  exact line_in_orthogonal_line dotForm (indicator S) (indicator T)
    (indicator_orthogonal_of_even S T heven)

theorem triple_line_is_complement {h : ℕ} (S : Finset (Fin h))
    (hS : S.card = 3) :
    IsCompl ((ZMod 2) ∙ indicator S)
      (((ZMod 2) ∙ indicator S).orthogonalBilin (dotForm : _)) := by
  have hnorm : dotForm (indicator S) (indicator S) ≠ 0 := by
    rw [indicator_triple_norm S hS]
    decide
  exact LinearMap.isCompl_span_singleton_orthogonal hnorm

end FrameLabels
end ExactFourier
end OAI
