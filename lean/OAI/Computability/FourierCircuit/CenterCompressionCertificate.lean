import OAI.Computability.FourierCircuit.CompressedInvocation
import OAI.Computability.FourierCircuit.CenterBankShift
import OAI.Computability.FourierCircuit.CenterFrameDirectionAudit
import OAI.Computability.FourierCircuit.CenterFrameAudit

/-!
# Consolidated certificate for the h = 24 centre-compression candidate

This file is an explicit review entry point for the current centre-line
proposal.  It combines four facts already proved in separate modules:

* the shifted `h`-coordinate centre map plus the ordered-neighbour side bank
  is an exact scalar identity;
* the eight-row invocation restores arbitrary centre and side values, and its
  inverse and three-invocation exchange are exact;
* one concrete h = 24 neighbour transition has labelled orthogonal-complement
  transports and the audited residual direction count;
* the resulting role width, saving, and normalized arithmetic are exact.

The theorem intentionally does not package these local facts as a complete
three-stage frame-labelled circuit.  The missing bridge is the global choice
of compatible labels and address permutations for every stage and every
physical role.
-/

namespace OAI
namespace ExactFourier
namespace CenterCompressionCertificate

open CenterCompression
open CompressedInvocation

section Scalar

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

theorem scalar_identity (x : CenterCompression.Triple h → K) :
    CompressedInvocation.OrderedPairs.RHom
          (CenterCompression.compressedG x) +
        CompressedInvocation.OrderedPairs.JHom
          (CompressedInvocation.OrderedPairs.V x) = x := by
  exact CompressedInvocation.OrderedPairs.identity x

theorem forward_restores
    (s : CompressedInvocation.State
      (CenterCompression.Triple h → K)
      (CompressedInvocation.OrderedPairs.SideBank h K)
    (Fin h → K)) :
    CompressedInvocation.eightRows
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        CompressedInvocation.OrderedPairs.JHom
        CompressedInvocation.OrderedPairs.V s =
      {s with y := s.y + s.x} := by
  exact CompressedInvocation.OrderedPairs.compressed_restore s

theorem inverse_restores
    (s : CompressedInvocation.State
      (CenterCompression.Triple h → K)
      (CompressedInvocation.OrderedPairs.SideBank h K)
    (Fin h → K)) :
    CompressedInvocation.inverseEightRows
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        CompressedInvocation.OrderedPairs.JHom
        CompressedInvocation.OrderedPairs.V s =
      {s with y := s.y - s.x} := by
  exact CompressedInvocation.OrderedPairs.compressed_inverse_restore s

theorem three_invocations_exchange
    (s : CompressedInvocation.State
      (CenterCompression.Triple h → K)
      (CompressedInvocation.OrderedPairs.SideBank h K)
    (Fin h → K)) :
    CompressedInvocation.threeInvocations
        CompressedInvocation.OrderedPairs.RHom
        CenterCompression.compressedG
        CompressedInvocation.OrderedPairs.JHom
        CompressedInvocation.OrderedPairs.V s =
      {s with x := -s.y, y := s.x} := by
  exact CompressedInvocation.OrderedPairs.compressed_exchange s

end Scalar

namespace H24

theorem bank_shift_square {K : Type*} [Field K] [CharZero K]
    (x : CenterCompression.Triple 24 → K) :
    CenterBankShift.shift (CenterBankShift.oldG x) =
      CenterCompression.compressedG x := by
  exact CenterBankShift.shift_oldG x

theorem bank_readout_square {K : Type*} [Field K] [CharZero K]
    (S : CenterCompression.Triple 24)
    (c : CenterBankShift.CenterBank 24 K) :
    CenterBankShift.oldR S c =
      CenterCompression.compressedR S (CenterBankShift.shift c) := by
  exact CenterBankShift.oldR_shift S c

theorem bank_update_square {K : Type*} [Field K] [CharZero K]
    (c : CenterBankShift.CenterBank 24 K)
    (x : CenterCompression.Triple 24 → K) :
    CenterBankShift.shift
        (c.1 + (CenterBankShift.oldG x).1,
          c.2 + (CenterBankShift.oldG x).2) =
      CenterBankShift.shift c + CenterCompression.compressedG x := by
  exact CenterBankShift.shift_old_update c x

theorem local_frame_and_direction_audit :
    (ZMod 2) ∙ CenterFrameCertificate.sourceLabel ≤
        ((ZMod 2) ∙ CenterFrameCertificate.targetLabel).orthogonalBilin
          (TensorFrameLabels.tensorDotForm (h := 24) : _) ∧
      Module.finrank (ZMod 2)
          (CenterRowGeneral.residual (h := 24)
            (StagePrefixAudit.prefixUnit (ι := Fin 1) 0)) = 24 ∧
      Module.finrank (ZMod 2)
          (CenterRowGeneral.residual (h := 24)
            (StagePrefixAudit.prefixH (h := 24) (by omega))) = 24 ∧
      Module.finrank (ZMod 2)
          (CenterRowGeneral.residual (h := 24)
            (StagePrefixAudit.prefixHH (h := 24) (by omega))) = 24 := by
  have hlocal := CenterFrameDirectionAudit.concrete_neighbour_direction_step
  have hcount := CenterFrameDirectionAudit.h24_centre_direction_count
  exact ⟨hlocal.1, hcount.1, hcount.2.1, hcount.2.2⟩

theorem exact_arithmetic :
    CenterCompression.H24.Wcompressed = 34666930287616 ∧
      CenterCompression.H24.deltaCompressed = 2425172992 ∧
      CenterCompression.H24.epsilonCompressed =
        2368333 / 474989023199232 := by
  exact ⟨CenterCompression.H24.Wcompressed_eq,
    CenterCompression.H24.deltaCompressed_eq,
    CenterCompression.H24.epsilonCompressed_eq⟩

theorem exact_directional_budget :
    CenterFrameAudit.H24.compressedW = 34666930287616 ∧
      CenterCompression.H24.deltaCompressed = 2425172992 := by
  exact ⟨CenterFrameAudit.H24.compressedW_eq,
    CenterCompression.H24.deltaCompressed_eq⟩

end H24
end CenterCompressionCertificate
end ExactFourier
end OAI
