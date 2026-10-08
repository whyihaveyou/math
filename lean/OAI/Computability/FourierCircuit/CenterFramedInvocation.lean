import OAI.Computability.FourierCircuit.CenterCompressionCertificate
import OAI.Computability.FourierCircuit.StagePrefixLabelAudit
import OAI.Computability.FourierCircuit.CenterFrameDirectionAudit

/-!
# A frame-labelled interface for the centre-compressed invocation

`CenterCompressionCertificate` proves the scalar eight-row identity, while
`StagePrefixLabelAudit` and `CenterFrameDirectionAudit` prove local frame
facts.  This file is the small bridge between those layers.  A
`PrefixFrame` records the unit prefix, the two active labels, the nested side
residual and the exact centre/side direction counts.  A `FramedState` carries
that certificate together with the arbitrary scalar banks used by the
compressed invocation.  The three invocation maps preserve the certificate
and their scalar projections satisfy the already-proved restoration laws.

The interface is intentionally local: it does not claim that all three
physical stages, address permutations, or the all-length recursive assembly
have been scheduled.  Those are separate obligations.
-/

namespace OAI
namespace ExactFourier
namespace CenterFramedInvocation

open CenterCompression
open CompressedInvocation
open StagePrefixLabelAudit
open StagePrefixAudit

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev PrefixAddress (h : ℕ) := Fin 1 × Fin h → F

/-! ## The prefix-labelled local stage -/

structure PrefixFrame (h : ℕ) where
  pre : Fin 1 → F
  source : Active h
  target : Active h
  prefix_unit : dotProduct pre pre = (1 : F)
  source_unit : dotProduct source source = (1 : F)
  target_unit : dotProduct target target = (1 : F)
  source_target_orthogonal : dotProduct source target = (0 : F)
  centre_is_compl : IsCompl
      (CenterRowGeneral.residual (h := h) pre)
      (CenterRowGeneral.parent pre)
  centre_directions : Module.finrank F
      (CenterRowGeneral.residual (h := h) pre) = h
  side_nested : SideRowGeneralArbitrary.residual (ι := Fin 1)
      pre source target ≤
      (StagePrefixLabelAudit.labelledStage pre source target
        prefix_unit source_unit source_target_orthogonal).residual
  side_directions : Module.finrank F
      (SideRowGeneralArbitrary.residual (ι := Fin 1)
        pre source target) = h - 2

theorem PrefixFrame.source_embedded_unit {h : ℕ} (f : PrefixFrame h) :
    dotProduct (embeddedLabel f.pre f.source)
      (embeddedLabel f.pre f.source) = (1 : F) := by
  exact embedded_unit f.pre f.source f.prefix_unit f.source_unit

theorem PrefixFrame.embedded_labels_orthogonal {h : ℕ} (f : PrefixFrame h) :
    dotProduct (embeddedLabel f.pre f.source)
      (embeddedLabel f.pre f.target) = (0 : F) := by
  exact embedded_orthogonal f.pre f.source f.target
    f.prefix_unit f.source_target_orthogonal

theorem PrefixFrame.centre_row_certificate {h : ℕ} (f : PrefixFrame h) :
    IsCompl (CenterRowGeneral.residual (h := h) f.pre)
      (CenterRowGeneral.parent f.pre) ∧
      Module.finrank F (CenterRowGeneral.residual (h := h) f.pre) = h := by
  exact ⟨f.centre_is_compl, f.centre_directions⟩

/-! ## The concrete first-prefix h = 24 certificate -/

def h24PrefixFrame : PrefixFrame 24 :=
  { pre := prefixUnit (ι := Fin 1) 0
    source := stageX (h := 24) (by norm_num)
    target := stageY (h := 24) (by norm_num)
    prefix_unit := prefixUnit_unit (ι := Fin 1) 0
    source_unit := xLabel_unit (h := 24) (by norm_num)
    target_unit := yLabel_unit (h := 24) (by norm_num)
    source_target_orthogonal := labels_orthogonal (h := 24) (by norm_num)
    centre_is_compl := CenterRowGeneral.row_isCompl
      (prefixUnit (ι := Fin 1) 0)
      (prefixUnit_unit (ι := Fin 1) 0)
    centre_directions := CenterRowGeneral.residual_finrank
      (prefixUnit (ι := Fin 1) 0) (prefixUnit_unit (ι := Fin 1) 0)
    side_nested := by
      exact (labelled_side_stage_certificate
        (p := prefixUnit (ι := Fin 1) 0)
        (x := stageX (h := 24) (by norm_num))
        (y := stageY (h := 24) (by norm_num))
        (prefixUnit_unit (ι := Fin 1) 0)
        (xLabel_unit (h := 24) (by norm_num))
        (yLabel_unit (h := 24) (by norm_num))
        (labels_orthogonal (h := 24) (by norm_num))
        (by norm_num)).2.2.1
    side_directions := SideRowGeneralArbitrary.residual_finrank
      (prefixUnit (ι := Fin 1) 0)
      (stageX (h := 24) (by norm_num))
      (stageY (h := 24) (by norm_num))
      (prefixUnit_unit (ι := Fin 1) 0)
      (xLabel_unit (h := 24) (by norm_num))
      (yLabel_unit (h := 24) (by norm_num))
      (labels_orthogonal (h := 24) (by norm_num))
      (by norm_num) }

theorem h24PrefixFrame_centre_count :
    Module.finrank F (CenterRowGeneral.residual (h := 24) h24PrefixFrame.pre) = 24 :=
  h24PrefixFrame.centre_directions

theorem h24PrefixFrame_side_count :
    Module.finrank F
        (SideRowGeneralArbitrary.residual (ι := Fin 1)
          h24PrefixFrame.pre h24PrefixFrame.source h24PrefixFrame.target) = 22 :=
  h24PrefixFrame.side_directions

theorem h24PrefixFrame_nested :
    SideRowGeneralArbitrary.residual (ι := Fin 1)
        h24PrefixFrame.pre h24PrefixFrame.source h24PrefixFrame.target ≤
      (StagePrefixLabelAudit.labelledStage h24PrefixFrame.pre
        h24PrefixFrame.source h24PrefixFrame.target
        h24PrefixFrame.prefix_unit h24PrefixFrame.source_unit
        h24PrefixFrame.source_target_orthogonal).residual :=
  h24PrefixFrame.side_nested

/-! ## Frame-labelled scalar invocation -/

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

abbrev ScalarState (h : ℕ) (K : Type*) :=
  CompressedInvocation.State (Triple h → K)
    (OrderedPairs.SideBank h K) (Fin h → K)

structure FramedState (h : ℕ) (K : Type*) [Field K] [CharZero K] where
  scalar : ScalarState h K
  frame : PrefixFrame h

noncomputable def forward (s : FramedState h K) : FramedState h K :=
  { scalar := CompressedInvocation.eightRows
      OrderedPairs.RHom compressedG OrderedPairs.JHom OrderedPairs.V s.scalar
    frame := s.frame }

noncomputable def inverse (s : FramedState h K) : FramedState h K :=
  { scalar := CompressedInvocation.inverseEightRows
      OrderedPairs.RHom compressedG OrderedPairs.JHom OrderedPairs.V s.scalar
    frame := s.frame }

noncomputable def exchange (s : FramedState h K) : FramedState h K :=
  { scalar := CompressedInvocation.threeInvocations
      OrderedPairs.RHom compressedG OrderedPairs.JHom OrderedPairs.V s.scalar
    frame := s.frame }

@[simp] theorem forward_frame (s : FramedState h K) :
    (forward s).frame = s.frame := rfl

@[simp] theorem inverse_frame (s : FramedState h K) :
    (inverse s).frame = s.frame := rfl

@[simp] theorem exchange_frame (s : FramedState h K) :
    (exchange s).frame = s.frame := rfl

theorem forward_scalar_restore (s : FramedState h K) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} := by
  exact CenterCompressionCertificate.forward_restores s.scalar

theorem inverse_scalar_restore (s : FramedState h K) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} := by
  exact CenterCompressionCertificate.inverse_restores s.scalar

theorem exchange_scalar (s : FramedState h K) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} := by
  exact CenterCompressionCertificate.three_invocations_exchange s.scalar

theorem forward_restore (s : FramedState h K) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} ∧
      (forward s).frame = s.frame := by
  exact ⟨forward_scalar_restore s, forward_frame s⟩

theorem inverse_restore (s : FramedState h K) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} ∧
      (inverse s).frame = s.frame := by
  exact ⟨inverse_scalar_restore s, inverse_frame s⟩

theorem exchange_restore (s : FramedState h K) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} ∧
      (exchange s).frame = s.frame := by
  exact ⟨exchange_scalar s, exchange_frame s⟩

/-! The concrete h = 24 frame can be attached to any scalar state. -/

def h24 (s : ScalarState 24 K) : FramedState 24 K :=
  { scalar := s, frame := h24PrefixFrame }

theorem h24_forward_restore (s : ScalarState 24 K) :
    (forward (h24 s)).scalar = {s with y := s.y + s.x} := by
  exact forward_scalar_restore (h24 s)

end CenterFramedInvocation
end ExactFourier
end OAI
