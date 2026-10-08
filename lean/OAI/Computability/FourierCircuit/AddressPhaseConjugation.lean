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
