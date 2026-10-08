import OAI.Computability.FourierCircuit.StagePrefixAudit
import OAI.Computability.FourierCircuit.StageResidualCertificate

/-!
# Frame-labelled prefix stage interface

`StagePrefixAudit` checks only the dimensions of the centre and side
residuals.  This file adds the missing local label interface: an active
source/target pair is embedded through a unit prefix line, the embedded
labels remain unit and orthogonal, and the side residual is contained in the
orthogonal complement of those two full address labels.  The inclusion is
deliberately the strongest statement available without choosing the paper's
complete frame schedule; its codomain can contain additional prefix
directions.  The exact side directional count is still `h - 2`.
-/

namespace OAI
namespace ExactFourier
namespace StagePrefixLabelAudit

open StagePrefixAudit

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}

/-- Embed an active label into the full prefix/active address space. -/
def embeddedLabel (p : ι → F) (a : Active h) : Address ι h :=
  CenterRowGeneral.insert p a

theorem embedded_dot (p : ι → F) (hp : dotProduct p p = (1 : F))
    (a b : Active h) :
    dotProduct (embeddedLabel p a) (embeddedLabel p b) = dotProduct a b := by
  exact CenterRowGeneral.insert_dot_insert p hp a b

theorem embedded_unit (p : ι → F) (a : Active h)
    (hp : dotProduct p p = (1 : F))
    (ha : dotProduct a a = (1 : F)) :
    dotProduct (embeddedLabel p a) (embeddedLabel p a) = (1 : F) := by
  rw [embedded_dot p hp, ha]

theorem embedded_orthogonal (p : ι → F) (a b : Active h)
    (hp : dotProduct p p = (1 : F))
    (hab : dotProduct a b = (0 : F)) :
    dotProduct (embeddedLabel p a) (embeddedLabel p b) = (0 : F) := by
  rw [embedded_dot p hp, hab]

/-- The two embedded labels as a reusable residual-stage certificate. -/
def labelledStage (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = (0 : F)) :
    StageResidual.Certificate (ι × Fin h) where
  source := embeddedLabel p x
  target := embeddedLabel p y
  source_unit := embedded_unit p x hp hx
  source_target_orthogonal := embedded_orthogonal p x y hp hxy

theorem labelledStage_decomposition (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = (0 : F)) :
    (labelledStage p x y hp hx hxy).parent =
      (labelledStage p x y hp hx hxy).removed ⊔
        (labelledStage p x y hp hx hxy).residual := by
  exact StageResidual.Certificate.decomposition _

theorem labelledStage_removed_le_parent (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = (0 : F)) :
    (labelledStage p x y hp hx hxy).removed ≤
      (labelledStage p x y hp hx hxy).parent := by
  exact StageResidual.Certificate.removed_le_parent _

/-- The side residual's inserted directions obey both embedded frame labels.

The target is the full-address two-label residual from `labelledStage`; the
inclusion can be strict because a general prefix space has extra directions.
-/
theorem side_residual_le_labelledStage_residual
    (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = (0 : F)) :
    SideRowGeneralArbitrary.residual (ι := ι) p x y ≤
      (labelledStage p x y hp hx hxy).residual := by
  rintro z ⟨r, rfl⟩
  change (SideRowGeneralArbitrary.insertPair (ι := ι) p x y) r ∈
    (Submodule.span F
      ({embeddedLabel p x, embeddedLabel p y} : Set (Address ι h))).orthogonalBilin
      (BinaryTransvection.bilinearDot : _)
  rw [Submodule.mem_orthogonalBilin_span]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · change dotProduct (embeddedLabel p x)
      (SideRowGeneralArbitrary.insertPair (ι := ι) p x y r) = 0
    change dotProduct (CenterRowGeneral.insert p x)
      (CenterRowGeneral.insert p r.1) = 0
    rw [CenterRowGeneral.insert_dot_insert p hp]
    exact (SideRowGeneralArbitrary.mem_pairPerp_iff.mp r.property).1
  · change dotProduct (embeddedLabel p y)
      (SideRowGeneralArbitrary.insertPair (ι := ι) p x y r) = 0
    change dotProduct (CenterRowGeneral.insert p y)
      (CenterRowGeneral.insert p r.1) = 0
    rw [CenterRowGeneral.insert_dot_insert p hp]
    exact (SideRowGeneralArbitrary.mem_pairPerp_iff.mp r.property).2

/-- The embedded side stage has the audited `h - 2` directional count. -/
theorem side_direction_count (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = (0 : F)) (hh : 2 ≤ h) :
    Module.finrank F (SideRowGeneralArbitrary.residual (ι := ι) p x y) = h - 2 := by
  exact SideRowGeneralArbitrary.residual_finrank p x y hp hx hy hxy hh

/-- A single theorem exposing all local label, nesting, and count obligations. -/
theorem labelled_side_stage_certificate (p : ι → F) (x y : Active h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = (0 : F)) (hh : 2 ≤ h) :
    dotProduct (embeddedLabel p x) (embeddedLabel p x) = (1 : F) ∧
      dotProduct (embeddedLabel p x) (embeddedLabel p y) = (0 : F) ∧
      SideRowGeneralArbitrary.residual (ι := ι) p x y ≤
        (labelledStage p x y hp hx hxy).residual ∧
      Module.finrank F (SideRowGeneralArbitrary.residual (ι := ι) p x y) = h - 2 := by
  exact ⟨embedded_unit p x hp hx,
    embedded_orthogonal p x y hp hxy,
    side_residual_le_labelledStage_residual p x y hp hx hy hxy,
    side_direction_count p x y hp hx hy hxy hh⟩

/-- Concrete first-prefix (`ι = Fin 1`) instance at the audited `h = 24`.

This is an actual labelled local stage: the prefix is the unit coordinate
line and the active labels are the first two coordinate lines.  It supplies a
checked source/target embedding, the two-label nesting condition, and the
codimension-two direction count.  It still makes no claim about the paper's
later address schedule.
-/
theorem h24_first_prefix_stage :
    let p : Fin 1 → F := prefixUnit (ι := Fin 1) 0
    let x : Active 24 := stageX (h := 24) (by norm_num)
    let y : Active 24 := stageY (h := 24) (by norm_num)
    dotProduct (embeddedLabel p x) (embeddedLabel p x) = (1 : F) ∧
      dotProduct (embeddedLabel p x) (embeddedLabel p y) = (0 : F) ∧
      SideRowGeneralArbitrary.residual (ι := Fin 1) p x y ≤
        (labelledStage (h := 24) p x y
          (prefixUnit_unit (ι := Fin 1) 0)
          (xLabel_unit (h := 24) (by norm_num))
          (labels_orthogonal (h := 24) (by norm_num))).residual ∧
      Module.finrank F (SideRowGeneralArbitrary.residual (ι := Fin 1) p x y) = 22 := by
  dsimp
  exact labelled_side_stage_certificate
    (p := prefixUnit (ι := Fin 1) 0)
    (x := stageX (h := 24) (by norm_num))
    (y := stageY (h := 24) (by norm_num))
    (prefixUnit_unit (ι := Fin 1) 0)
    (xLabel_unit (h := 24) (by norm_num))
    (yLabel_unit (h := 24) (by norm_num))
    (labels_orthogonal (h := 24) (by norm_num))
    (by norm_num)

end StagePrefixLabelAudit
end ExactFourier
end OAI
