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

@[simp] theorem signCharacter_one : signCharacter (1 : F2) = (-1 : ℂ) := by
  norm_num [signCharacter, AddChar.zmodChar_apply, ZMod.val_one]

noncomputable def entry {ι : Type} [Fintype ι] (x y : Address ι) : ℂ :=
  signCharacter (dotProduct x y)

/-! The dot-product character with frequency `a`. -/
noncomputable def dotChar {ι : Type} [Fintype ι]
    (a : Address ι) : AddChar (Address ι) ℂ where
  toFun := fun x => signCharacter (dotProduct x a)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    rw [add_dotProduct, signCharacter_add]

@[simp] theorem dotChar_apply {ι : Type} [Fintype ι]
    (a x : Address ι) : dotChar a x = entry x a := rfl

/-! A nonzero frequency gives a nontrivial additive character. -/
theorem dotChar_ne_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {a : Address ι} (ha : a ≠ 0) : dotChar a ≠ 1 := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hval := congrArg (fun ψ : AddChar (Address ι) ℂ => ψ (coordinate i)) h
  have hsign : signCharacter (a i) = 1 := by
    simpa [dotChar, coordinate_dot] using hval
  have hcases : a i = (0 : F2) ∨ a i = (1 : F2) := by
    have hlt : (a i).val < 2 := ZMod.val_lt (a i)
    have hv : (a i).val = 0 ∨ (a i).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl ((ZMod.val_eq_zero (a i)).mp hv)
    · right
      apply ZMod.val_injective 2
      exact hv
  rcases hcases with hz | hone
  · exact hi hz
  · have hone' : signCharacter (1 : F2) = 1 := by simpa [hone] using hsign
    rw [signCharacter_one] at hone'
    norm_num at hone'

theorem dotChar_sum_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {a : Address ι} (ha : a ≠ 0) :
    (∑ x : Address ι, dotChar a x) = 0 := by
  exact AddChar.sum_eq_zero_of_ne_one (dotChar_ne_one ha)

theorem entry_mul_entry_eq_dotChar_add
    {ι : Type} [Fintype ι] (a b x : Address ι) :
    entry x a * entry x b = dotChar (a + b) x := by
  change signCharacter (dotProduct x a) * signCharacter (dotProduct x b) =
    signCharacter (dotProduct x (a + b))
  rw [dotProduct_add, signCharacter_add]

theorem signCharacter_sq (z : F2) :
    signCharacter z * signCharacter z = 1 := by
  calc
    signCharacter z * signCharacter z = signCharacter (z + z) :=
      (signCharacter_add z z).symm
    _ = 1 := by rw [CharTwo.add_self_eq_zero, signCharacter_zero]

theorem entry_sq {ι : Type} [Fintype ι] (x a : Address ι) :
    entry x a * entry x a = 1 := by
  exact signCharacter_sq (dotProduct x a)

theorem walsh_sum_eq_zero_of_ne
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : Address ι} (hab : a ≠ b) :
    (∑ x : Address ι, entry x a * entry x b) = 0 := by
  have hab0 : a + b ≠ 0 := by
    intro hz
    apply hab
    have hbb : b + b = (0 : Address ι) := by
      ext i
      exact CharTwo.add_self_eq_zero (b i)
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [hbb]
      _ = (a + b) + b := by rw [add_assoc]
      _ = 0 + b := by rw [hz]
      _ = b := by simp
  calc
    (∑ x : Address ι, entry x a * entry x b) =
        ∑ x : Address ι, dotChar (a + b) x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact entry_mul_entry_eq_dotChar_add a b x
    _ = 0 := dotChar_sum_zero hab0

theorem walsh_sum_eq_card_of_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Address ι) :
    (∑ x : Address ι, entry x a * entry x a) =
      (Fintype.card (Address ι) : ℂ) := by
  calc
    (∑ x : Address ι, entry x a * entry x a) =
        ∑ _x : Address ι, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact entry_sq x a
    _ = (Fintype.card (Address ι) : ℂ) := by simp

theorem walsh_sum_orthogonality
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : Address ι) :
    (∑ x : Address ι, entry x a * entry x b) =
      if a = b then (Fintype.card (Address ι) : ℂ) else 0 := by
  by_cases hab : a = b
  · subst b
    simp [walsh_sum_eq_card_of_eq]
  · simp [walsh_sum_eq_zero_of_ne hab, hab]

/-! The unnormalised Walsh matrix indexed by binary addresses. -/
noncomputable def matrix {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix (Address ι) (Address ι) ℂ := fun x y => entry x y

/-! The character sums give the exact Gram identity for the unnormalised
Walsh matrix.  The scalar is the address cardinality; no square-root
normalisation is hidden here. -/
theorem transpose_mul_matrix
    {ι : Type} [Fintype ι] [DecidableEq ι] :
    matrix.transpose * matrix =
      (Fintype.card (Address ι) : ℂ) •
        (1 : Matrix (Address ι) (Address ι) ℂ) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  change (∑ j : Address ι, entry j a * entry j b) = _
  rw [walsh_sum_orthogonality]
  by_cases hab : a = b <;> simp [hab]

/-! The unnormalised Walsh matrix is invertible.  This only uses that the
address cardinality is a nonzero complex scalar and the Gram identity above. -/
theorem matrix_isUnit
    {ι : Type} [Fintype ι] [DecidableEq ι] : IsUnit (matrix :
      Matrix (Address ι) (Address ι) ℂ) := by
  rw [isUnit_iff_exists_inv']
  refine ⟨(Fintype.card (Address ι) : ℂ)⁻¹ • matrix.transpose, ?_⟩
  rw [Matrix.smul_mul, transpose_mul_matrix]
  have hcard : Fintype.card (Address ι) ≠ 0 := Fintype.card_ne_zero
  have hcardC : (Fintype.card (Address ι) : ℂ) ≠ 0 := by
    exact_mod_cast hcard
  simp [smul_smul, hcardC]

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

/-- The concrete Walsh frame commutes with every dot-product-preserving
address permutation.  This is the explicit `hJ` premise needed by the framed
phase theorem. -/
theorem scaledMatrix_commutes_of_orthogonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι) (horth : IsOrthogonal e) (c : ℂ) :
    BinaryAddressPermutation.matrix e * scaledMatrix c =
      scaledMatrix c * BinaryAddressPermutation.matrix e := by
  have hunit : IsUnit (BinaryAddressPermutation.matrix e) :=
    MonomialMatrix.unit _ (BinaryAddressPermutation.matrix_monomial e)
  have hinvR : BinaryAddressPermutation.matrix e *
      (BinaryAddressPermutation.matrix e)⁻¹ =
      (1 : Matrix (Address ι) (Address ι) ℂ) :=
    Matrix.mul_nonsing_inv _
      (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit)
  have hinvL : (BinaryAddressPermutation.matrix e)⁻¹ *
      BinaryAddressPermutation.matrix e =
      (1 : Matrix (Address ι) (Address ι) ℂ) :=
    Matrix.nonsing_inv_mul _
      (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit)
  calc
    BinaryAddressPermutation.matrix e * scaledMatrix c =
        (BinaryAddressPermutation.matrix e * scaledMatrix c *
        (BinaryAddressPermutation.matrix e)⁻¹) *
          BinaryAddressPermutation.matrix e := by
            symm
            calc
              (BinaryAddressPermutation.matrix e * scaledMatrix c *
                  (BinaryAddressPermutation.matrix e)⁻¹) *
                  BinaryAddressPermutation.matrix e =
                  BinaryAddressPermutation.matrix e * scaledMatrix c *
                    ((BinaryAddressPermutation.matrix e)⁻¹ *
                      BinaryAddressPermutation.matrix e) := by
                rw [Matrix.mul_assoc]
              _ = BinaryAddressPermutation.matrix e * scaledMatrix c := by
                rw [hinvL, Matrix.mul_one]
    _ = scaledMatrix c * BinaryAddressPermutation.matrix e := by
      rw [scaledMatrix_conj_isOrthogonal e horth c]

/-- The exact Gram factor for an arbitrary scalar normalisation. -/
theorem scaledMatrix_transpose_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) :
    (scaledMatrix c).transpose * scaledMatrix c =
      (c * c * (Fintype.card (Address ι) : ℂ)) •
        (1 : Matrix (Address ι) (Address ι) ℂ) := by
  simp only [scaledMatrix, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, transpose_mul_matrix, smul_smul]
  ring

/-- If a chosen scalar satisfies the exact square-root equation, the scaled
Walsh matrix has identity Gram matrix.  The scalar equation is left explicit
so that no analytic square-root convention is hidden in this algebraic file.
-/
theorem scaledMatrix_transpose_mul_eq_one
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (hc : c * c * (Fintype.card (Address ι) : ℂ) = 1) :
    (scaledMatrix c).transpose * scaledMatrix c =
      (1 : Matrix (Address ι) (Address ι) ℂ) := by
  rw [scaledMatrix_transpose_mul, hc, one_smul]

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
