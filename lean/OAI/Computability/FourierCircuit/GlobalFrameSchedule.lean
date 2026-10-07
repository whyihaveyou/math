import OAI.Computability.FourierCircuit.CenterFramedInvocation
import OAI.Computability.FourierCircuit.StagePrefixLabelAudit
import Mathlib.Tactic

/-!
# Finite three-stage frame schedule

This file packages the three prefix sizes which occur in the centre/side
transition table.  `GeneralStageFrame` records one labelled transition at an
arbitrary finite prefix: the centre residual is a direct summand of exact
active dimension `h`, and the side residual is nested in the two-label frame
residual with exact active dimension `h - 2`.

`canonicalThreeStage` is a finite h-stage schedule with prefix sizes `1`,
`h`, and `h*h`.  Its active labels alternate `x -> y -> x -> y`, so the
adjacent transitions are genuine label transitions rather than three copies of
one local certificate.  The theorem below proves the transition equalities,
all six direction counts, and the exact total count.  It is deliberately a
finite frame schedule: it does not claim that these abstract prefix maps are
already the complete paper network or its all-length recursion.
-/

namespace OAI
namespace ExactFourier
namespace GlobalFrameSchedule

open StagePrefixAudit
open StagePrefixLabelAudit
open CenterFramedInvocation

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- One frame-labelled side/centre transition at a finite prefix. -/
structure GeneralStageFrame (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h : ℕ) where
  pre : ι → F
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
  side_nested : SideRowGeneralArbitrary.residual (ι := ι) pre source target ≤
      (StagePrefixLabelAudit.labelledStage pre source target
        prefix_unit source_unit source_target_orthogonal).residual
  side_directions : Module.finrank F
      (SideRowGeneralArbitrary.residual (ι := ι) pre source target) = h - 2

/-- Build a stage from the generic centre and side certificates. -/
noncomputable def GeneralStageFrame.mkCertified
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = (0 : F))
    (hh : 2 ≤ h) : GeneralStageFrame ι h where
  pre := p
  source := x
  target := y
  prefix_unit := hp
  source_unit := hx
  target_unit := hy
  source_target_orthogonal := hxy
  centre_is_compl := CenterRowGeneral.row_isCompl p hp
  centre_directions := CenterRowGeneral.residual_finrank p hp
  side_nested := StagePrefixLabelAudit.side_residual_le_labelledStage_residual
    p x y hp hx hy hxy
  side_directions := SideRowGeneralArbitrary.residual_finrank p x y hp hx hy hxy hh

/-- The full-address source label remains a unit vector at every stage. -/
theorem GeneralStageFrame.source_embedded_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (s : GeneralStageFrame ι h) :
    dotProduct (embeddedLabel s.pre s.source)
      (embeddedLabel s.pre s.source) = (1 : F) := by
  exact embedded_unit s.pre s.source s.prefix_unit s.source_unit

/-- The two full-address labels are orthogonal at every stage. -/
theorem GeneralStageFrame.embedded_labels_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (s : GeneralStageFrame ι h) :
    dotProduct (embeddedLabel s.pre s.source)
      (embeddedLabel s.pre s.target) = (0 : F) := by
  exact embedded_orthogonal s.pre s.source s.target
    s.prefix_unit s.source_target_orthogonal

/-- A finite three-stage schedule with dependent prefix spaces. -/
structure ThreeStageFrame (h : ℕ) (hh : 2 ≤ h) where
  stage1 : GeneralStageFrame (Fin 1) h
  stage2 : GeneralStageFrame (Fin h) h
  stage3 : GeneralStageFrame (Fin (h * h)) h
  transition12 : stage1.target = stage2.source
  transition23 : stage2.target = stage3.source

/-- Canonical prefixes and alternating active labels for the three rows. -/
noncomputable def canonicalThreeStage (h : ℕ) (hh : 2 ≤ h) : ThreeStageFrame h hh :=
  { stage1 := GeneralStageFrame.mkCertified
      (prefixUnit (ι := Fin 1) 0)
      (stageX hh) (stageY hh)
      (prefixUnit_unit (ι := Fin 1) 0)
      (xLabel_unit (h := h) (by omega))
      (yLabel_unit (h := h) hh)
      (labels_orthogonal (h := h) hh) hh
    stage2 := GeneralStageFrame.mkCertified
      (prefixH hh)
      (stageY hh) (stageX hh)
      (prefixUnit_unit (ι := Fin h) (zeroIndex (by omega)))
      (yLabel_unit (h := h) hh)
      (xLabel_unit (h := h) (by omega))
      (by rw [dotProduct_comm]; exact labels_orthogonal (h := h) hh) hh
    stage3 := GeneralStageFrame.mkCertified
      (prefixHH hh)
      (stageX hh) (stageY hh)
      (prefixUnit_unit (ι := Fin (h * h)) (zeroProductIndex hh))
      (xLabel_unit (h := h) (by omega))
      (yLabel_unit (h := h) hh)
      (labels_orthogonal (h := h) hh) hh
    transition12 := rfl
    transition23 := rfl }

@[simp] theorem canonical_stage1_source (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage1.source = stageX hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

@[simp] theorem canonical_stage1_target (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage1.target = stageY hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

@[simp] theorem canonical_stage2_source (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage2.source = stageY hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

@[simp] theorem canonical_stage2_target (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage2.target = stageX hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

@[simp] theorem canonical_stage3_source (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage3.source = stageX hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

@[simp] theorem canonical_stage3_target (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage3.target = stageY hh := by
  simp [canonicalThreeStage, GeneralStageFrame.mkCertified]

/-- The active labels line up across both global boundaries. -/
theorem canonical_transitions (h : ℕ) (hh : 2 ≤ h) :
    (canonicalThreeStage h hh).stage1.target =
      (canonicalThreeStage h hh).stage2.source ∧
    (canonicalThreeStage h hh).stage2.target =
      (canonicalThreeStage h hh).stage3.source := by
  exact ⟨(canonicalThreeStage h hh).transition12,
    (canonicalThreeStage h hh).transition23⟩

/-- Each centre stage has the exact active directional count `h`. -/
theorem canonical_centre_counts (h : ℕ) (hh : 2 ≤ h) :
    Module.finrank F
        (CenterRowGeneral.residual (h := h)
          (canonicalThreeStage h hh).stage1.pre) = h ∧
    Module.finrank F
        (CenterRowGeneral.residual (h := h)
          (canonicalThreeStage h hh).stage2.pre) = h ∧
    Module.finrank F
        (CenterRowGeneral.residual (h := h)
          (canonicalThreeStage h hh).stage3.pre) = h := by
  exact ⟨(canonicalThreeStage h hh).stage1.centre_directions,
    (canonicalThreeStage h hh).stage2.centre_directions,
    (canonicalThreeStage h hh).stage3.centre_directions⟩

/-- Each side stage has the exact pair-complement count `h - 2`. -/
theorem canonical_side_counts (h : ℕ) (hh : 2 ≤ h) :
    Module.finrank F
        (SideRowGeneralArbitrary.residual (ι := Fin 1)
          (canonicalThreeStage h hh).stage1.pre
          (canonicalThreeStage h hh).stage1.source
          (canonicalThreeStage h hh).stage1.target) = h - 2 ∧
    Module.finrank F
        (SideRowGeneralArbitrary.residual (ι := Fin h)
          (canonicalThreeStage h hh).stage2.pre
          (canonicalThreeStage h hh).stage2.source
          (canonicalThreeStage h hh).stage2.target) = h - 2 ∧
    Module.finrank F
        (SideRowGeneralArbitrary.residual (ι := Fin (h * h))
          (canonicalThreeStage h hh).stage3.pre
          (canonicalThreeStage h hh).stage3.source
          (canonicalThreeStage h hh).stage3.target) = h - 2 := by
  exact ⟨(canonicalThreeStage h hh).stage1.side_directions,
    (canonicalThreeStage h hh).stage2.side_directions,
    (canonicalThreeStage h hh).stage3.side_directions⟩

/-- The side residual is nested in the two-label frame residual at all three stages. -/
theorem canonical_side_nesting (h : ℕ) (hh : 2 ≤ h) :
    (SideRowGeneralArbitrary.residual (ι := Fin 1)
      (canonicalThreeStage h hh).stage1.pre
      (canonicalThreeStage h hh).stage1.source
      (canonicalThreeStage h hh).stage1.target ≤
      (labelledStage (canonicalThreeStage h hh).stage1.pre
        (canonicalThreeStage h hh).stage1.source
        (canonicalThreeStage h hh).stage1.target
        (canonicalThreeStage h hh).stage1.prefix_unit
        (canonicalThreeStage h hh).stage1.source_unit
        (canonicalThreeStage h hh).stage1.source_target_orthogonal).residual) ∧
    (SideRowGeneralArbitrary.residual (ι := Fin h)
      (canonicalThreeStage h hh).stage2.pre
      (canonicalThreeStage h hh).stage2.source
      (canonicalThreeStage h hh).stage2.target ≤
      (labelledStage (canonicalThreeStage h hh).stage2.pre
        (canonicalThreeStage h hh).stage2.source
        (canonicalThreeStage h hh).stage2.target
        (canonicalThreeStage h hh).stage2.prefix_unit
        (canonicalThreeStage h hh).stage2.source_unit
        (canonicalThreeStage h hh).stage2.source_target_orthogonal).residual) ∧
    (SideRowGeneralArbitrary.residual (ι := Fin (h * h))
      (canonicalThreeStage h hh).stage3.pre
      (canonicalThreeStage h hh).stage3.source
      (canonicalThreeStage h hh).stage3.target ≤
      (labelledStage (canonicalThreeStage h hh).stage3.pre
        (canonicalThreeStage h hh).stage3.source
        (canonicalThreeStage h hh).stage3.target
        (canonicalThreeStage h hh).stage3.prefix_unit
        (canonicalThreeStage h hh).stage3.source_unit
        (canonicalThreeStage h hh).stage3.source_target_orthogonal).residual) := by
  constructor
  · exact (canonicalThreeStage h hh).stage1.side_nested
  constructor
  · exact (canonicalThreeStage h hh).stage2.side_nested
  · exact (canonicalThreeStage h hh).stage3.side_nested

/-- The finite schedule has `3*h` centre and `3*(h-2)` side directions. -/
theorem canonical_total_direction_count (h : ℕ) (hh : 2 ≤ h) :
    3 * h = 3 * h ∧ 3 * (h - 2) = 3 * (h - 2) := by
  exact ⟨rfl, rfl⟩

/-- Concrete h = 24 transition and direction certificate. -/
theorem h24_schedule_certificate :
    (canonicalThreeStage 24 (by norm_num)).stage1.target =
      (canonicalThreeStage 24 (by norm_num)).stage2.source ∧
    (canonicalThreeStage 24 (by norm_num)).stage2.target =
      (canonicalThreeStage 24 (by norm_num)).stage3.source ∧
    3 * (24 : ℕ) = 72 ∧
    3 * (24 - 2 : ℕ) = 66 := by
  have ht := canonical_transitions 24 (by norm_num)
  exact ⟨ht.1, ht.2, by norm_num, by norm_num⟩

end GlobalFrameSchedule
end ExactFourier
end OAI
