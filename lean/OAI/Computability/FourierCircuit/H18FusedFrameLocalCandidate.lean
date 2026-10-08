import OAI.Computability.FourierCircuit.FusedFrameLocalCertificate
import OAI.Computability.FourierCircuit.FusedCentreBoundaryArithmeticH18

/-!
# h = 18 fused-centre frame-local candidate

The arithmetic stress test at `h = 18` clears the `10⁻⁹` scale, while the
generic fused-frame certificate proves the scalar restoration and the local
binary-label readout at one fixed prefix.  This file instantiates the latter
at `h = 18` and records the two facts together.

This remains a conditional local candidate.  It does not provide a legal
complex gate, scalar/gate commutation, a shared global DAG, or an all-length
DFT theorem.  The arithmetic margin and the frame certificate are therefore
reported separately from those still-open implementation obligations.
-/

namespace OAI
namespace ExactFourier
namespace H18FusedFrameLocalCandidate

open CenterFramedInvocation
open FusedFrameLocalCertificate
open StagePrefixLabelAudit
open StagePrefixAudit
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

/-! ## The concrete h = 18 first-prefix frame -/

def h18PrefixFrame : PrefixFrame 18 :=
  { pre := prefixUnit (ι := Fin 1) 0
    source := stageX (h := 18) (by norm_num)
    target := stageY (h := 18) (by norm_num)
    prefix_unit := prefixUnit_unit (ι := Fin 1) 0
    source_unit := xLabel_unit (h := 18) (by norm_num)
    target_unit := yLabel_unit (h := 18) (by norm_num)
    source_target_orthogonal := labels_orthogonal (h := 18) (by norm_num)
    centre_is_compl := CenterRowGeneral.row_isCompl
      (prefixUnit (ι := Fin 1) 0)
      (prefixUnit_unit (ι := Fin 1) 0)
    centre_directions := CenterRowGeneral.residual_finrank
      (prefixUnit (ι := Fin 1) 0) (prefixUnit_unit (ι := Fin 1) 0)
    side_nested := by
      exact (labelled_side_stage_certificate
        (p := prefixUnit (ι := Fin 1) 0)
        (x := stageX (h := 18) (by norm_num))
        (y := stageY (h := 18) (by norm_num))
        (prefixUnit_unit (ι := Fin 1) 0)
        (xLabel_unit (h := 18) (by norm_num))
        (yLabel_unit (h := 18) (by norm_num))
        (labels_orthogonal (h := 18) (by norm_num))
        (by norm_num)).2.2.1
    side_directions := SideRowGeneralArbitrary.residual_finrank
      (prefixUnit (ι := Fin 1) 0)
      (stageX (h := 18) (by norm_num))
      (stageY (h := 18) (by norm_num))
      (prefixUnit_unit (ι := Fin 1) 0)
      (xLabel_unit (h := 18) (by norm_num))
      (yLabel_unit (h := 18) (by norm_num))
      (labels_orthogonal (h := 18) (by norm_num))
      (by norm_num) }

theorem h18PrefixFrame_centre_count :
    Module.finrank F
        (CenterRowGeneral.residual (h := 18) h18PrefixFrame.pre) = 18 :=
  h18PrefixFrame.centre_directions

theorem h18PrefixFrame_side_count :
    Module.finrank F
        (SideRowGeneralArbitrary.residual (ι := Fin 1)
          h18PrefixFrame.pre h18PrefixFrame.source h18PrefixFrame.target) = 16 :=
  h18PrefixFrame.side_directions

theorem h18PrefixFrame_labels :
    dotProduct (embeddedLabel h18PrefixFrame.pre h18PrefixFrame.source)
        (embeddedLabel h18PrefixFrame.pre h18PrefixFrame.source) = (1 : F) ∧
      dotProduct (embeddedLabel h18PrefixFrame.pre h18PrefixFrame.source)
        (embeddedLabel h18PrefixFrame.pre h18PrefixFrame.target) = (0 : F) := by
  exact ⟨h18PrefixFrame.source_embedded_unit,
    h18PrefixFrame.embedded_labels_orthogonal⟩

/-! ## The frame-labelled scalar candidate -/

variable {K : Type*} [Field K] [CharZero K]

def h18Framed
    (s : CenterFramedInvocation.ScalarState 18 K) :
    CenterFramedInvocation.FramedState 18 K :=
  { scalar := s, frame := h18PrefixFrame }

theorem h18_fused_restore
    (s : CenterFramedInvocation.ScalarState 18 K) :
    (FusedFrameLocalCertificate.fusedForward (h18Framed s)).scalar =
        {s with y := s.y + s.x} ∧
      (FusedFrameLocalCertificate.fusedForward (h18Framed s)).frame =
        h18PrefixFrame := by
  exact ⟨FusedFrameLocalCertificate.fusedForward_scalar_update
      (h18Framed s),
    FusedFrameLocalCertificate.fusedForward_frame (h18Framed s)⟩

theorem h18_fused_readout
    {ι : Type*} [Fintype ι]
    (s : CenterFramedInvocation.ScalarState 18 K)
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (w : Fin 18) (hw : h18PrefixFrame.target w = 0)
    (z : Address ι 18)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p h18PrefixFrame.source) :
    z +
          CenterBoundaryTensorLift.lift
            (unitCoordinateEquiv h18PrefixFrame.target w
              h18PrefixFrame.target_unit hw)
            (CenterRowGeneral.insert p h18PrefixFrame.target) ∈
        SideRowGeneralArbitrary.L5 p h18PrefixFrame.target := by
  exact FusedFrameLocalCertificate.lifted_readout_legal
    { framed := h18Framed s
      pre := p
      pre_unit := hp
      witness := w
      witness_zero := hw
      source_row := z
      source_row_mem := hz }

theorem h18_valid
    {ι : Type*} [Fintype ι]
    (s : CenterFramedInvocation.ScalarState 18 K)
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (w : Fin 18) (hw : h18PrefixFrame.target w = 0)
    (z : Address ι 18)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p h18PrefixFrame.source) :
    (FusedFrameLocalCertificate.fusedForward (h18Framed s)).scalar =
        {s with y := s.y + s.x} ∧
      (FusedFrameLocalCertificate.fusedForward (h18Framed s)).frame =
        h18PrefixFrame ∧
      z +
          CenterBoundaryTensorLift.lift
            (unitCoordinateEquiv h18PrefixFrame.target w
              h18PrefixFrame.target_unit hw)
            (CenterRowGeneral.insert p h18PrefixFrame.target) ∈
        SideRowGeneralArbitrary.L5 p h18PrefixFrame.target := by
  exact ⟨(h18_fused_restore s).1, (h18_fused_restore s).2,
    h18_fused_readout s p hp w hw z hz⟩

/-! ## The numerical claim remains explicitly conditional -/

theorem h18_normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 <
      FusedCentreBoundaryArithmeticH18.normalized :=
  FusedCentreBoundaryArithmeticH18.normalized_gt_one_e_minus_nine

end H18FusedFrameLocalCandidate
end ExactFourier
end OAI
