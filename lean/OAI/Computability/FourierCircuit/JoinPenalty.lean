import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Finite-dimensional cost of joining two independent frame lines

A side-wire grouping that must contain two disjoint nonzero one-dimensional
labels has a two-dimensional join.  This file isolates that geometric fact
from the Fourier construction.  It is the finite-dimensional statement needed
before charging residual coordinates in a concrete frame implementation.
-/

namespace OAI
namespace ExactFourier
namespace JoinPenalty

/-- A common frame containing two disjoint nonzero lines has dimension at least
    two, so two line-removal charges total at least two. -/
theorem join_cost_at_least_two
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (x y : V) (hx : x ≠ 0) (hy : y ≠ 0)
    (hdisj : Disjoint (K ∙ x) (K ∙ y))
    (J : Submodule K V) (hjoin : (K ∙ x) ⊔ (K ∙ y) ≤ J) :
    2 ≤ (Module.finrank K J - 1) + (Module.finrank K J - 1) := by
  have hxi : Module.finrank K (K ∙ x) = 1 := finrank_span_singleton hx
  have hyi : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy
  have hInf : (K ∙ x) ⊓ (K ∙ y) = ⊥ := hdisj.eq_bot
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ x) (K ∙ y)
  have hInfDim : Module.finrank K ↥((K ∙ x) ⊓ (K ∙ y)) = 0 := by
    rw [hInf, finrank_bot K V]
  rw [hxi, hyi, hInfDim, add_zero] at hsum
  have hmono : Module.finrank K ↥((K ∙ x) ⊔ (K ∙ y)) ≤ Module.finrank K J :=
    Submodule.finrank_mono hjoin
  rw [hsum] at hmono
  omega

end JoinPenalty
end ExactFourier
end OAI
