import OAI.Computability.FourierCircuit.BinaryAddressPermutation
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

/-!
# An explicit binary Walsh matrix

This file gives a concrete, unnormalised Walsh matrix on the binary address
space `Address ι := ι → ZMod 2`.  Its entries are the standard sign character
of the dot product.  We prove the exact invariance needed by the address phase
interface for every linear equivalence preserving that dot product.

No frame is identified with this matrix, and no normalisation or circuit cost
claim is made.  A scalar multiple can be used whenever a later construction
chooses a Walsh normalisation.
-/

namespace OAI
namespace ExactFourier
namespace BinaryWalsh

open BinaryAddressPermutation
open BinaryTransvection

abbrev F2 := BinaryAddressPermutation.F2
abbrev Address (ι : Type) := BinaryAddressPermutation.Address ι

/-! The order-two additive character `0 ↦ 1`, `1 ↦ -1`. -/
noncomputable def signCharacter : AddChar F2 ℂ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℂ)) (by norm_num)

@[simp] theorem signCharacter_zero : signCharacter (0 : F2) = 1 := by
  exact AddChar.map_zero_eq_one _

theorem signCharacter_add (a b : F2) :
    signCharacter (a + b) = signCharacter a * signCharacter b := by
  exact AddChar.map_add_eq_mul _ _ _

noncomputable def entry {ι : Type} [Fintype ι] (x y : Address ι) : ℂ :=
  signCharacter (dotProduct x y)

/-! The unnormalised Walsh matrix indexed by binary addresses. -/
noncomputable def matrix {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix (Address ι) (Address ι) ℂ := fun x y => entry x y

/-! A linear address change is orthogonal when it preserves the binary dot
product.  This is the only hypothesis needed for Walsh invariance. -/
def IsOrthogonal {ι : Type} [Fintype ι]
    (e : Address ι ≃ₗ[F2] Address ι) : Prop :=
  ∀ x y, dotProduct (e x) (e y) = dotProduct x y

theorem dot_symm_preserved {ι : Type} [Fintype ι]
    (e : Address ι ≃ₗ[F2] Address ι) (horth : IsOrthogonal e)
    (x y : Address ι) :
    dotProduct (e.symm x) (e.symm y) = dotProduct x y := by
  have h := horth (e.symm x) (e.symm y)
  simpa using h.symm

/-! Conjugating the Walsh matrix by an orthogonal address permutation leaves it
unchanged.  The proof uses the generic monomial reindexing theorem and the
dot-product preservation hypothesis only for the inverse equivalence. -/
theorem matrix_conj_isOrthogonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι) (horth : IsOrthogonal e) :
    BinaryAddressPermutation.matrix e * matrix *
        (BinaryAddressPermutation.matrix e)⁻¹ = matrix := by
  rw [BinaryAddressPermutation.matrix_conj]
  ext x y
  change signCharacter (dotProduct (e.symm x) (e.symm y)) =
    signCharacter (dotProduct x y)
  rw [dot_symm_preserved e horth]

/-! Any scalar normalisation of the Walsh matrix has the same invariance. -/
noncomputable def scaledMatrix
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) :
    Matrix (Address ι) (Address ι) ℂ := c • matrix

theorem scaledMatrix_conj_isOrthogonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι) (horth : IsOrthogonal e) (c : ℂ) :
    BinaryAddressPermutation.matrix e * scaledMatrix c *
        (BinaryAddressPermutation.matrix e)⁻¹ = scaledMatrix c := by
  simp only [scaledMatrix, Matrix.mul_smul, Matrix.smul_mul,
    matrix_conj_isOrthogonal e horth]

/-! The centre-edge coordinate equivalence is therefore a concrete Walsh
invariance instance. -/
theorem unitCoordinate_matrix_conj
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → F2) (w : ι)
    (ht : dotProduct t t = (1 : F2)) (hw : t w = 0) :
    BinaryAddressPermutation.matrix (unitCoordinateEquiv t w ht hw) * matrix *
        (BinaryAddressPermutation.matrix (unitCoordinateEquiv t w ht hw))⁻¹ = matrix := by
  apply matrix_conj_isOrthogonal
  intro x y
  exact unitCoordinateEquiv_dot t w ht hw x y

end BinaryWalsh
end ExactFourier
end OAI
