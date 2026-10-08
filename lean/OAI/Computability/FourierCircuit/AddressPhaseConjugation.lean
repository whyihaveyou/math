import OAI.Computability.FourierCircuit.BinaryAddressPermutation
import OAI.Computability.FourierCircuit.BinaryTransvection
import Mathlib.Tactic

/-!
# Phase diagonals under free binary address changes

The frame labels in the exact DFT construction are binary address data, while
phase profiles live on the complex array address set.  This file records the
precise compatibility statement needed before introducing a concrete Walsh
frame: conjugating a diagonal phase profile by the monomial matrix induced by
a binary address equivalence simply relabels that profile.  No map from
`ZMod 2` into `ℂ` is used.

The result is local.  It does not identify a phase profile with a quadratic
label, nor does it assert a global circuit schedule or a directional cost.
-/

namespace OAI
namespace ExactFourier
namespace AddressPhaseConjugation

open BinaryAddressPermutation

abbrev F2 := BinaryAddressPermutation.F2
abbrev Address (ι : Type) := BinaryAddressPermutation.Address ι

/-- A diagonal complex phase profile on an address space. -/
noncomputable def phaseDiagonal {ι : Type} (q : Address ι → ℂ) :
    Matrix (Address ι) (Address ι) ℂ := by
  classical
  exact Matrix.diagonal q

/-- Free binary address changes relabel diagonal phase profiles exactly. -/
theorem matrix_conj_phaseDiagonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (q : Address ι → ℂ) :
    matrix e * phaseDiagonal q * (matrix e)⁻¹ =
      phaseDiagonal (q ∘ (fun x => (induced e).symm x)) := by
  rw [matrix_conj]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [phaseDiagonal]
  · have h' : (induced e).symm i ≠ (induced e).symm j := by
      intro h
      apply hij
      exact (induced e).symm.injective h
    simp [phaseDiagonal, hij, h']

/-- A Walsh-style framed phase has the form `J * diag(q) * J`.  If the
    address permutation commutes with the common frame `J` on both sides,
    conjugation still only relabels the phase profile.  The two commutation
    hypotheses are explicit because this file does not choose a particular
    Walsh normalization or prove orthogonality of `J`. -/
noncomputable def framedPhase
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q : Address ι → ℂ) : Matrix (Address ι) (Address ι) ℂ := by
  classical
  exact J * phaseDiagonal q * J

theorem matrix_commutes_inverse_of
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (hJ : matrix e * J = J * matrix e) :
    J * (matrix e)⁻¹ = (matrix e)⁻¹ * J := by
  have hunit : IsUnit (matrix e) :=
    MonomialMatrix.unit _ (matrix_monomial e)
  have hinvL : (matrix e)⁻¹ * matrix e =
      (1 : Matrix (Address ι) (Address ι) ℂ) :=
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit)
  have hinvR : matrix e * (matrix e)⁻¹ =
      (1 : Matrix (Address ι) (Address ι) ℂ) :=
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit)
  calc
    J * (matrix e)⁻¹ =
        (1 : Matrix (Address ι) (Address ι) ℂ) * (J * (matrix e)⁻¹) := by
          rw [Matrix.one_mul]
    _ = ((matrix e)⁻¹ * matrix e) * (J * (matrix e)⁻¹) := by
          rw [hinvL]
    _ = (matrix e)⁻¹ * (matrix e * J) * (matrix e)⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = (matrix e)⁻¹ * (J * matrix e) * (matrix e)⁻¹ := by
          rw [hJ]
    _ = ((matrix e)⁻¹ * J) * (matrix e * (matrix e)⁻¹) := by
          simp only [Matrix.mul_assoc]
    _ = (matrix e)⁻¹ * J := by
          rw [hinvR, Matrix.mul_one]

theorem matrix_conj_framedPhase
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q : Address ι → ℂ)
    (hJ : matrix e * J = J * matrix e)
    (hJinv : J * (matrix e)⁻¹ = (matrix e)⁻¹ * J) :
    matrix e * framedPhase J q * (matrix e)⁻¹ =
      framedPhase J (q ∘ (fun x => (induced e).symm x)) := by
  change matrix e * (J * phaseDiagonal q * J) * (matrix e)⁻¹ =
    J * phaseDiagonal (q ∘ (fun x => (induced e).symm x)) * J
  calc
    matrix e * (J * phaseDiagonal q * J) * (matrix e)⁻¹ =
        (matrix e * J) * phaseDiagonal q * J * (matrix e)⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = (J * matrix e) * phaseDiagonal q * J * (matrix e)⁻¹ := by
          rw [hJ]
    _ = J * (matrix e * phaseDiagonal q * (matrix e)⁻¹) * J := by
          simp only [Matrix.mul_assoc]
          rw [hJinv]
    _ = J * phaseDiagonal (q ∘ (fun x => (induced e).symm x)) * J := by
          rw [matrix_conj_phaseDiagonal]

theorem matrix_conj_framedPhase_of_commutes
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q : Address ι → ℂ)
    (hJ : matrix e * J = J * matrix e) :
    matrix e * framedPhase J q * (matrix e)⁻¹ =
      framedPhase J (q ∘ (fun x => (induced e).symm x)) := by
  exact matrix_conj_framedPhase e J q hJ
    (matrix_commutes_inverse_of e J hJ)

/-- A phase profile that is invariant under an address change commutes with
    the corresponding free monomial matrix. -/
theorem matrix_commutes_phaseDiagonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Address ι ≃ₗ[F2] Address ι)
    (q : Address ι → ℂ)
    (hq : q ∘ (fun x => (induced e).symm x) = q) :
    matrix e * phaseDiagonal q = phaseDiagonal q * matrix e := by
  have hconj := matrix_conj_phaseDiagonal e q
  rw [hq] at hconj
  have hinv : (matrix e)⁻¹ * matrix e = (1 : Matrix (Address ι) (Address ι) ℂ) := by
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp
      (MonomialMatrix.unit _ (matrix_monomial e)))
  calc
    matrix e * phaseDiagonal q =
        (matrix e * phaseDiagonal q) * ((matrix e)⁻¹ * matrix e) := by
          rw [hinv, Matrix.mul_one]
    _ = (matrix e * phaseDiagonal q * (matrix e)⁻¹) * matrix e := by
          simp only [Matrix.mul_assoc]
    _ = phaseDiagonal q * matrix e := by rw [hconj]

open BinaryTransvection

/-! The centre-edge coordinate change is the concrete transvection used by the
selective frame certificates.  Exposing it here makes the phase correction
available at exactly the same interface as the binary label transport. -/

theorem unitCoordinate_matrix_conj_phaseDiagonal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → F2) (w : ι)
    (ht : dotProduct t t = (1 : F2)) (hw : t w = 0)
    (q : Address ι → ℂ) :
    matrix (unitCoordinateEquiv t w ht hw) * phaseDiagonal q *
        (matrix (unitCoordinateEquiv t w ht hw))⁻¹ =
      phaseDiagonal
        (q ∘ (fun x => (induced (unitCoordinateEquiv t w ht hw)).symm x)) := by
  exact matrix_conj_phaseDiagonal (unitCoordinateEquiv t w ht hw) q

end AddressPhaseConjugation
end ExactFourier
end OAI
