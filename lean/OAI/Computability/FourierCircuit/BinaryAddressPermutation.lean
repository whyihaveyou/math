import OAI.Computability.FourierCircuit.BinaryTransvection
import OAI.Computability.FourierCircuit.MonomialTools
import Mathlib.Tactic

/-!
# Binary frame maps as address permutations

The binary frame labels live in `F₂` and index complex array addresses; they
are not complex data vectors.  A binary linear equivalence therefore induces
an address permutation on the complex array.  This file records the exact
semantic bridge that is available without postulating an additive map
`F₂ → ℂ`: its permutation matrix is monomial and conjugates matrix units by
the corresponding address permutation.

This is the bridge needed for the paper's free address changes.  It does not
claim that a binary transvection is itself a charged complex shear; a charged
step still needs the nested-label `Φ_V Φ_U⁻¹` factorization from the paper.
-/

namespace OAI
namespace ExactFourier
namespace BinaryAddressPermutation

abbrev F2 := ZMod 2
abbrev Address (ι : Type*) := ι → F2

variable {ι : Type}

/-- The address permutation induced by a binary linear equivalence. -/
noncomputable def induced (e : Address ι ≃ₗ[F2] Address ι) : Equiv.Perm (Address ι) :=
  e.toEquiv

/-- The corresponding complex permutation matrix on array addresses. -/
noncomputable def matrix [DecidableEq (Address ι)]
    (e : Address ι ≃ₗ[F2] Address ι) :
    Matrix (Address ι) (Address ι) ℂ :=
  permM (induced e)

@[simp] theorem matrix_eq_permM [DecidableEq (Address ι)]
    (e : Address ι ≃ₗ[F2] Address ι) :
    matrix e = permM (induced e) := rfl

/-- A binary address change is free monomial work on the complex array. -/
theorem matrix_monomial [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι) :
    MonomialMatrix (matrix e) := by
  exact permM_monomial (induced e)

/-- Its inverse is the permutation induced by the inverse binary map. -/
theorem matrix_inv [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι) :
    (matrix e)⁻¹ = matrix e.symm := by
  rw [matrix, matrix, permM_inv]
  rfl

/-- Conjugation transports a complex matrix along the address permutation. -/
theorem matrix_conj [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (X : Matrix (Address ι) (Address ι) ℂ) :
    matrix e * X * (matrix e)⁻¹ =
      X.submatrix (induced e).symm (induced e).symm := by
  exact permM_conj (induced e) X

/-- Matrix units are transported exactly, with no support-map assumption. -/
theorem matrix_conj_single [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (a b : Address ι) :
    matrix e * Matrix.single a b (1 : ℂ) * (matrix e)⁻¹ =
      Matrix.single (induced e a) (induced e b) 1 := by
  exact permM_conj_single (induced e) a b


end BinaryAddressPermutation
end ExactFourier
end OAI
