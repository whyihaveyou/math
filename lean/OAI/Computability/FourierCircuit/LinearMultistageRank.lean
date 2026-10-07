import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Generic rank obstruction for linear multi-stage side banks

If a linear map on a finite-dimensional source is factored through `q` copies
of an auxiliary bank `R`, its rank is at most `q * finrank R`. In particular,
a surjective correction on an `n`-dimensional space requires at least `n`
total auxiliary coordinates. This is the abstract rank step used by the
exact Johnson-scheme side audit; the h=24 invertibility certificate itself is
kept as an exact finite script.
-/

namespace OAI
namespace ExactFourier
namespace LinearMultistageRank

open scoped BigOperators

section

variable {K X R : Type*} [Field K]
variable [AddCommGroup X] [Module K X]
variable [AddCommGroup R] [Module K R]
variable [FiniteDimensional K X] [FiniteDimensional K R]

/-- Add the outputs of `q` linear readouts on a product bank. -/
def bankReadout (q : ℕ) (J : Fin q → R →ₗ[K] X) :
    (Fin q → R) →ₗ[K] X :=
  { toFun := fun a => ∑ i, J i (a i)
    map_add' := by
      intro a b
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      simp only [Pi.smul_apply, map_smul]
      rw [← Finset.smul_sum]
      rfl }

/-- Place `q` source-to-bank maps side by side. -/
def bankInput (q : ℕ) (V : Fin q → X →ₗ[K] R) :
    X →ₗ[K] (Fin q → R) :=
  LinearMap.pi V

/-- Every additive q-stage factorisation has rank at most q times bank rank. -/
theorem finrank_range_factorization_le (q : ℕ)
    (J : Fin q → R →ₗ[K] X) (V : Fin q → X →ₗ[K] R)
    (A : X →ₗ[K] X)
    (hfactor : A = (bankReadout q J).comp (bankInput q V)) :
    Module.finrank K A.range ≤ q * Module.finrank K R := by
  rw [hfactor]
  have hprod : Module.finrank K (Fin q → R) = q * Module.finrank K R := by
    simp [Module.finrank_pi_fintype]
  have hrange :
      ((bankReadout q J).comp (bankInput q V)).range ≤ (bankReadout q J).range :=
    LinearMap.range_comp_le_range _ _
  have hdim :
      Module.finrank K ((bankReadout q J).comp (bankInput q V)).range ≤
        Module.finrank K (bankReadout q J).range :=
    Submodule.finrank_mono hrange
  exact le_trans hdim <| le_trans
    (bankReadout q J).finrank_range_le
    (le_of_eq hprod)

/-- A surjective factorisation needs at least as many bank coordinates as the
source dimension. -/
theorem finrank_surjective_factorization_le (q : ℕ)
    (J : Fin q → R →ₗ[K] X) (V : Fin q → X →ₗ[K] R)
    (A : X →ₗ[K] X) (hsurj : Function.Surjective A)
    (hfactor : A = (bankReadout q J).comp (bankInput q V)) :
    Module.finrank K X ≤ q * Module.finrank K R := by
  have htop : A.range = ⊤ := (LinearMap.range_eq_top).2 hsurj
  have hdim : Module.finrank K A.range = Module.finrank K X := by
    rw [htop, finrank_top]
  rw [← hdim]
  exact finrank_range_factorization_le q J V A hfactor

end
end LinearMultistageRank
end ExactFourier
end OAI
