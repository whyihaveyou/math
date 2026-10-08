import OAI.Computability.FourierCircuit.BinaryWalsh
import OAI.Computability.FourierCircuit.AddressPhaseConjugation
import Mathlib.Tactic

/-!
# Walsh framed-phase composition

This file supplies the algebraic composition lemmas needed for a concrete
`Phi` ratio.  `BinaryWalsh` gives an unnormalised Walsh matrix and an explicit
scalar normalisation equation; `AddressPhaseConjugation` gives the common
`J * diag(q) * J` phase form.  The results below establish, under the stated
normalisation, involutivity of `J`, multiplication of framed phases by pointwise
phase multiplication, and the corresponding pointwise quotient formula.

No claim about a binary quadratic phase profile, a gate schedule, or operation
counts is made here.
-/

namespace OAI
namespace ExactFourier
namespace WalshPhaseComposition

open BinaryAddressPermutation
open BinaryWalsh
open AddressPhaseConjugation

abbrev F2 := BinaryWalsh.F2
abbrev Address (ι : Type) := BinaryWalsh.Address ι

/-! The binary Walsh matrix is symmetric because the binary dot product is
commutative. -/
theorem matrix_transpose_eq_matrix
    {ι : Type} [Fintype ι] [DecidableEq ι] :
    (BinaryWalsh.matrix : Matrix (Address ι) (Address ι) ℂ).transpose =
      BinaryWalsh.matrix := by
  ext x y
  change BinaryWalsh.entry y x = BinaryWalsh.entry x y
  simp only [BinaryWalsh.entry]
  rw [dotProduct_comm]

/-! A normalised Walsh matrix squares to the identity. -/
theorem scaledMatrix_mul_self_eq_one
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (hc : c * c * (Fintype.card (Address ι) : ℂ) = 1) :
    BinaryWalsh.scaledMatrix c * BinaryWalsh.scaledMatrix c =
      (1 : Matrix (Address ι) (Address ι) ℂ) := by
  have hgram := BinaryWalsh.scaledMatrix_transpose_mul_eq_one c hc
  rw [show (BinaryWalsh.scaledMatrix c).transpose =
      BinaryWalsh.scaledMatrix c by
        simp only [BinaryWalsh.scaledMatrix, Matrix.transpose_smul,
          matrix_transpose_eq_matrix]] at hgram
  exact hgram

/-! The diagonal phase profiles multiply pointwise. -/
theorem phaseDiagonal_mul
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q r : Address ι → ℂ) :
    AddressPhaseConjugation.phaseDiagonal q *
        AddressPhaseConjugation.phaseDiagonal r =
      AddressPhaseConjugation.phaseDiagonal (fun x => q x * r x) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [AddressPhaseConjugation.phaseDiagonal]
  · simp [AddressPhaseConjugation.phaseDiagonal, hxy]

/-! Two framed phases compose by pointwise multiplication whenever the frame
is involutive. -/
theorem framedPhase_mul
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q r : Address ι → ℂ)
    (hJJ : J * J = (1 : Matrix (Address ι) (Address ι) ℂ)) :
    AddressPhaseConjugation.framedPhase J q *
        AddressPhaseConjugation.framedPhase J r =
      AddressPhaseConjugation.framedPhase J (fun x => q x * r x) := by
  change (J * AddressPhaseConjugation.phaseDiagonal q * J) *
      (J * AddressPhaseConjugation.phaseDiagonal r * J) = _
  rw [show (J * AddressPhaseConjugation.phaseDiagonal q * J) *
      (J * AddressPhaseConjugation.phaseDiagonal r * J) =
      J * AddressPhaseConjugation.phaseDiagonal q * (J * J) *
        AddressPhaseConjugation.phaseDiagonal r * J by
        simp only [Matrix.mul_assoc]]
  rw [hJJ, Matrix.mul_one]
  change J * AddressPhaseConjugation.phaseDiagonal q *
      AddressPhaseConjugation.phaseDiagonal r * J =
    J * AddressPhaseConjugation.phaseDiagonal (fun x => q x * r x) * J
  rw [Matrix.mul_assoc J, phaseDiagonal_mul]

/-! The involutive frame sends the constant-one profile to the identity. -/
theorem framedPhase_one
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Address ι) (Address ι) ℂ)
    (hJJ : J * J = (1 : Matrix (Address ι) (Address ι) ℂ)) :
    AddressPhaseConjugation.framedPhase J (fun _ => (1 : ℂ)) =
      (1 : Matrix (Address ι) (Address ι) ℂ) := by
  change J * AddressPhaseConjugation.phaseDiagonal (fun _ => (1 : ℂ)) * J = _
  simp only [AddressPhaseConjugation.phaseDiagonal, Matrix.diagonal_one]
  simpa using hJJ

/-! Pointwise nonzero phases have the expected framed inverse. -/
theorem framedPhase_inv
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Address ι) (Address ι) ℂ)
    (r : Address ι → ℂ)
    (hJJ : J * J = (1 : Matrix (Address ι) (Address ι) ℂ))
    (hr : ∀ x, r x ≠ 0) :
    (AddressPhaseConjugation.framedPhase J r)⁻¹ =
      AddressPhaseConjugation.framedPhase J (fun x => (r x)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [framedPhase_mul J r (fun x => (r x)⁻¹) hJJ]
  rw [show (fun x => r x * (r x)⁻¹) = (fun _ => (1 : ℂ)) by
    funext x
    exact mul_inv_cancel₀ (hr x)]
  exact framedPhase_one J hJJ

/-! The concrete `Phi` ratio is therefore a pointwise quotient. -/
theorem framedPhase_mul_inv_eq_div
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q r : Address ι → ℂ)
    (hJJ : J * J = (1 : Matrix (Address ι) (Address ι) ℂ))
    (hr : ∀ x, r x ≠ 0) :
    AddressPhaseConjugation.framedPhase J q *
        (AddressPhaseConjugation.framedPhase J r)⁻¹ =
      AddressPhaseConjugation.framedPhase J (fun x => q x / r x) := by
  rw [framedPhase_inv J r hJJ hr]
  rw [framedPhase_mul J q (fun x => (r x)⁻¹) hJJ]
  congr 1

end WalshPhaseComposition
end ExactFourier
end OAI
