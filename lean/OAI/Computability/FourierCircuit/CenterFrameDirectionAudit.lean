import OAI.Computability.FourierCircuit.CenterFrameCertificate
import OAI.Computability.FourierCircuit.BinaryTransvection
import OAI.Computability.FourierCircuit.StagePrefixAudit
import Mathlib.Tactic.NormNum

/-!
# Concrete centre-direction transport audit

This module records the part of the h = 24 frame audit that can be discharged
without the full eight-row schedule.  For the concrete source and target
triple labels used by `CenterFrameCertificate`, coordinate 23 lies outside
both supports.  The explicit characteristic-two transvection therefore
transports each labelled orthogonal complement to the corresponding coordinate
hyperplane.  The final theorem combines these transports with the existing
neighbour-line inclusion and the stage-prefix finrank certificate.

It is a local frame certificate: it does not assert a complete framed circuit
or an all-length Fourier theorem.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterFrameDirectionAudit

open CenterFrameCertificate
open FrameLabels

abbrev H := 24
abbrev V := Fin H → ZMod 2
abbrev w : Fin H := 23

abbrev sourceVec : V := indicator sourceA
abbrev targetVec : V := indicator targetA

lemma sourceVec_unit : dotProduct sourceVec sourceVec = (1 : ZMod 2) := by
  change FrameLabels.dotForm (indicator sourceA) (indicator sourceA) = (1 : ZMod 2)
  simpa [FrameLabels.dotForm, BinaryTransvection.bilinearDot] using
    (FrameLabels.indicator_triple_norm sourceA sourceA_card)

lemma targetVec_unit : dotProduct targetVec targetVec = (1 : ZMod 2) := by
  change FrameLabels.dotForm (indicator targetA) (indicator targetA) = (1 : ZMod 2)
  simpa [FrameLabels.dotForm, BinaryTransvection.bilinearDot] using
    (FrameLabels.indicator_triple_norm targetA targetA_card)

lemma sourceVec_zero_at_w : sourceVec w = 0 := by
  simp [sourceVec, w, sourceA, indicator]

lemma targetVec_zero_at_w : targetVec w = 0 := by
  simp [targetVec, w, targetA, indicator]

abbrev z : Fin H := 22

lemma targetVec_zero_at_z : targetVec z = 0 := by
  simp [targetVec, z, targetA, indicator]

lemma source_target_vec_orthogonal :
    dotProduct sourceVec targetVec = (0 : ZMod 2) := by
  change FrameLabels.dotForm (indicator sourceA) (indicator targetA) = (0 : ZMod 2)
  have heven : Even (targetA ∩ sourceA).card := by
    simpa [Finset.inter_comm] using source_target_even
  simpa [FrameLabels.dotForm, BinaryTransvection.bilinearDot, dotProduct_comm]
    using (FrameLabels.indicator_orthogonal_of_even targetA sourceA heven)

noncomputable abbrev sourceTransport : V ≃ₗ[ZMod 2] V :=
  BinaryTransvection.unitCoordinateEquiv sourceVec w sourceVec_unit sourceVec_zero_at_w

noncomputable abbrev targetTransport : V ≃ₗ[ZMod 2] V :=
  BinaryTransvection.unitCoordinateEquiv targetVec w targetVec_unit targetVec_zero_at_w

/-- The source triple complement is exactly a transported coordinate
    hyperplane; this gives an explicit frame basis transport target. -/
theorem source_complement_transport :
    (((ZMod 2) ∙ sourceVec).orthogonalBilin
        (BinaryTransvection.bilinearDot : _)).comap sourceTransport.toLinearMap =
      BinaryTransvection.coordinateHyperplane w := by
  exact BinaryTransvection.unitCoordinateEquiv_comap_orthogonal
    sourceVec w sourceVec_unit sourceVec_zero_at_w

/-- The target triple complement has the same explicit transport. -/
theorem target_complement_transport :
    (((ZMod 2) ∙ targetVec).orthogonalBilin
        (BinaryTransvection.bilinearDot : _)).comap targetTransport.toLinearMap =
      BinaryTransvection.coordinateHyperplane w := by
  exact BinaryTransvection.unitCoordinateEquiv_comap_orthogonal
    targetVec w targetVec_unit targetVec_zero_at_w

/-- The chosen coordinate transports the labelled lines to coordinate lines. -/
theorem source_line_transport : sourceTransport (BinaryTransvection.coordinate w) = sourceVec := by
  exact BinaryTransvection.unitCoordinateEquiv_coordinate
    sourceVec w sourceVec_unit sourceVec_zero_at_w

theorem target_line_transport : targetTransport (BinaryTransvection.coordinate w) = targetVec := by
  exact BinaryTransvection.unitCoordinateEquiv_coordinate
    targetVec w targetVec_unit targetVec_zero_at_w

noncomputable abbrev pairTransport : V ≃ₗ[ZMod 2] V :=
  BinaryTransvection.twoCoordinateEquiv sourceVec targetVec w z
    sourceVec_unit targetVec_unit sourceVec_zero_at_w targetVec_zero_at_z

/-- The two labelled directions have an explicit codimension-two coordinate
    transport.  This is the finite h = 24 instance of the side residual frame
    step used by the stage audit. -/
theorem pair_complement_transport :
    (BinaryTransvection.coordinateHyperplaneTwo w z).comap
        pairTransport.toLinearMap =
      (Submodule.span (ZMod 2) ({sourceVec, targetVec} : Set V)).orthogonalBilin
        (BinaryTransvection.bilinearDot : _) := by
  exact BinaryTransvection.twoCoordinateEquiv_comap_orthogonal
    sourceVec targetVec w z sourceVec_unit targetVec_unit
    source_target_vec_orthogonal sourceVec_zero_at_w targetVec_zero_at_w
    targetVec_zero_at_z (by decide)

/-- The concrete source-to-target neighbour step is compatible with both the
    line inclusion and explicit complement transports. -/
theorem concrete_neighbour_direction_step :
    (ZMod 2) ∙ sourceLabel ≤
        ((ZMod 2) ∙ targetLabel).orthogonalBilin (TensorFrameLabels.tensorDotForm (h := H) : _) ∧
      (((ZMod 2) ∙ sourceVec).orthogonalBilin
          (BinaryTransvection.bilinearDot : _)).comap sourceTransport.toLinearMap =
        BinaryTransvection.coordinateHyperplane w ∧
      (((ZMod 2) ∙ targetVec).orthogonalBilin
          (BinaryTransvection.bilinearDot : _)).comap targetTransport.toLinearMap =
        BinaryTransvection.coordinateHyperplane w ∧
      (BinaryTransvection.coordinateHyperplaneTwo w z).comap
          pairTransport.toLinearMap =
        (Submodule.span (ZMod 2) ({sourceVec, targetVec} : Set V)).orthogonalBilin
          (BinaryTransvection.bilinearDot : _) := by
  exact ⟨centre_neighbor_removed_le_parent, source_complement_transport,
    target_complement_transport, pair_complement_transport⟩

/-- At h = 24 each of the three centre prefix sizes has exactly 24 residual
    directions.  This is the direction-step count used by the arithmetic
    centre loss; the statement is intentionally separate from a full schedule.
-/
theorem h24_centre_direction_count :
    (Module.finrank (ZMod 2)
      (CenterRowGeneral.residual (h := 24)
        (StagePrefixAudit.prefixUnit (ι := Fin 1) 0))) = 24 ∧
    (Module.finrank (ZMod 2)
      (CenterRowGeneral.residual (h := 24)
        (StagePrefixAudit.prefixH (h := 24) (by omega)))) = 24 ∧
    (Module.finrank (ZMod 2)
      (CenterRowGeneral.residual (h := 24)
        (StagePrefixAudit.prefixHH (h := 24) (by omega)))) = 24 := by
  have h := StagePrefixAudit.prefix_finranks (h := 24) (by omega)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end CenterFrameDirectionAudit
end ExactFourier
end OAI
