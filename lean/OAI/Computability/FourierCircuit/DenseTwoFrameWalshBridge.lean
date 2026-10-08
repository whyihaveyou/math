import OAI.Computability.FourierCircuit.DenseTwoFrameComplexBridge
import OAI.Computability.FourierCircuit.BinaryWalsh
import OAI.Computability.FourierCircuit.AddressPhaseConjugation
import Mathlib.Tactic

/-!
# Dense two-frame Walsh compatibility

The dense two-frame route already has a binary orthogonal equivalence and a
free complex address-permutation semantics.  This file connects those two
facts to the concrete binary Walsh matrix already present in the repository.
The result is an exact frame-compatibility certificate: the lifted dense swap
commutes with every scalar-normalised Walsh matrix and therefore conjugates a
Walsh-framed phase by only relabelling its address profile.

This is still a local algebraic bridge.  It does not construct the charged
complex shear, a scalar-gate schedule, or the all-length DFT recurrence.
-/

namespace OAI
namespace ExactFourier
namespace DenseTwoFrameWalshBridge

open DenseTwoFrameComplexBridge
open CenterBoundaryTensorLift
open BinaryAddressPermutation
open BinaryWalsh
open AddressPhaseConjugation

abbrev F2 := ZMod 2
abbrev Address (ι : Type) (h : ℕ) := ι × Fin h → F2

/-- The lifted dense swap is orthogonal on the full binary address space. -/
theorem denseSwap_lift_isOrthogonal
    {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    BinaryWalsh.IsOrthogonal
      (CenterBoundaryTensorLift.lift (ι := ι)
        (denseSwap h hh heven)) := by
  intro x y
  exact denseSwap_lift_dot hh heven x y

/-- Every scalar-normalised concrete Walsh matrix commutes with the dense
address permutation. -/
theorem denseSwap_scaledWalsh_commutes
    {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h) (c : ℂ) :
    BinaryAddressPermutation.matrix
        (ι := ι × Fin h)
        (CenterBoundaryTensorLift.lift (ι := ι)
          (denseSwap h hh heven)) *
        BinaryWalsh.scaledMatrix c =
      BinaryWalsh.scaledMatrix c *
        BinaryAddressPermutation.matrix
          (ι := ι × Fin h)
          (CenterBoundaryTensorLift.lift (ι := ι)
            (denseSwap h hh heven)) := by
  exact BinaryWalsh.scaledMatrix_commutes_of_orthogonal
    (CenterBoundaryTensorLift.lift (ι := ι)
      (denseSwap h hh heven))
    (denseSwap_lift_isOrthogonal hh heven) c

/-- Conjugating a Walsh-framed phase by the dense swap only relabels its
address profile.  The proof uses the concrete Walsh commutation certificate
above and the generic framed-phase conjugation theorem. -/
theorem denseSwap_framedPhase_conj
    {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h)
    (c : ℂ) (q : Address ι h → ℂ) :
    BinaryAddressPermutation.matrix
        (ι := ι × Fin h)
        (CenterBoundaryTensorLift.lift (ι := ι)
          (denseSwap h hh heven)) *
        AddressPhaseConjugation.framedPhase
          (BinaryWalsh.scaledMatrix c) q *
        (BinaryAddressPermutation.matrix
          (ι := ι × Fin h)
          (CenterBoundaryTensorLift.lift (ι := ι)
            (denseSwap h hh heven)))⁻¹ =
      AddressPhaseConjugation.framedPhase
        (BinaryWalsh.scaledMatrix c)
        (q ∘ (fun x =>
          (BinaryAddressPermutation.induced
            (CenterBoundaryTensorLift.lift (ι := ι)
              (denseSwap h hh heven))).symm x)) := by
  exact AddressPhaseConjugation.matrix_conj_framedPhase_of_commutes
    (CenterBoundaryTensorLift.lift (ι := ι)
      (denseSwap h hh heven))
    (BinaryWalsh.scaledMatrix c) q
    (denseSwap_scaledWalsh_commutes hh heven c)

end DenseTwoFrameWalshBridge
end ExactFourier
end OAI
