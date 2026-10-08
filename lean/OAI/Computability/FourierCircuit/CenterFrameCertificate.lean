import OAI.Computability.FourierCircuit.TensorFrameLabels

/-!
# Concrete h = 24 frame-label transition

This file discharges one concrete neighbour/centre line transition for the
h = 24 tensor frame.  It is deliberately local: it proves the binary
orthogonal-complement decomposition for a chosen source and target label, but
it does not claim that the whole eight-row circuit or its address schedule has
been formalised.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterFrameCertificate

open TensorFrameLabels

abbrev H := 24
abbrev Addr := Fin H × (Fin H × Fin H)

/-- Two disjoint first-factor triples.  The other two factors are the same
    unit triple, so orthogonality is witnessed by the first tensor factor. -/
def sourceA : Finset (Fin H) := {(0 : Fin H), 1, 2}
def targetA : Finset (Fin H) := {(3 : Fin H), 4, 5}
def fixedB : Finset (Fin H) := {(0 : Fin H), 1, 2}
def fixedC : Finset (Fin H) := {(0 : Fin H), 1, 2}

theorem sourceA_card : sourceA.card = 3 := by
  norm_num [sourceA]

theorem targetA_card : targetA.card = 3 := by
  norm_num [targetA]

theorem fixedB_card : fixedB.card = 3 := by
  norm_num [fixedB]

theorem fixedC_card : fixedC.card = 3 := by
  norm_num [fixedC]

theorem source_target_disjoint : Disjoint sourceA targetA := by
  simp [sourceA, targetA]

theorem source_target_even : Even (sourceA ∩ targetA).card := by
  rw [Finset.disjoint_iff_inter_eq_empty.mp source_target_disjoint]
  simp

/-- The concrete source and target pure-tensor labels used by the transition. -/
def sourceLabel : Addr → ZMod 2 :=
  tensor3 sourceA fixedB fixedC

def targetLabel : Addr → ZMod 2 :=
  tensor3 targetA fixedB fixedC

theorem source_unit :
    tensorDotForm sourceLabel sourceLabel = (1 : ZMod 2) := by
  unfold sourceLabel
  exact tensor3_norm_of_triples sourceA fixedB fixedC
    sourceA_card fixedB_card fixedC_card

theorem source_target_orthogonal :
    tensorDotForm sourceLabel targetLabel = (0 : ZMod 2) := by
  unfold sourceLabel targetLabel
  exact tensor3_orthogonal_of_even sourceA fixedB fixedC targetA fixedB fixedC
    source_target_even

/-- Concrete centre-to-neighbour residual decomposition.  The parent line is
    the orthogonal complement of the target label; one source line is removed,
    leaving exactly the complement of the two labelled directions. -/
theorem centre_neighbor_decomposition :
    ((ZMod 2) ∙ targetLabel).orthogonalBilin (tensorDotForm : _) =
      (ZMod 2) ∙ sourceLabel ⊔
        (Submodule.span (ZMod 2) ({sourceLabel, targetLabel} :
          Set (Addr → ZMod 2))).orthogonalBilin (tensorDotForm : _) := by
  exact pure3_pair_complement_decomp
    (FrameLabels.indicator sourceA)
    (FrameLabels.indicator fixedB)
    (FrameLabels.indicator fixedC)
    (FrameLabels.indicator targetA)
    (FrameLabels.indicator fixedB)
    (FrameLabels.indicator fixedC)
    (by
      change FrameLabels.dotForm (FrameLabels.indicator sourceA)
        (FrameLabels.indicator sourceA) = (1 : ZMod 2)
      exact FrameLabels.indicator_triple_norm sourceA sourceA_card)
    (by
      change FrameLabels.dotForm (FrameLabels.indicator fixedB)
        (FrameLabels.indicator fixedB) = (1 : ZMod 2)
      exact FrameLabels.indicator_triple_norm fixedB fixedB_card)
    (by
      change FrameLabels.dotForm (FrameLabels.indicator fixedC)
        (FrameLabels.indicator fixedC) = (1 : ZMod 2)
      exact FrameLabels.indicator_triple_norm fixedC fixedC_card)
    (by
      exact FrameLabels.indicator_orthogonal_of_even sourceA targetA source_target_even)

/-- The same transition, phrased as a line inclusion, is the direction-step
    obligation needed before charging a source line against its target parent. -/
theorem centre_neighbor_removed_le_parent :
    (ZMod 2) ∙ sourceLabel ≤
      ((ZMod 2) ∙ targetLabel).orthogonalBilin (tensorDotForm : _) := by
  exact TensorFrameLabels.tensor3_neighbour_line_nested
    sourceA fixedB fixedC targetA fixedB fixedC source_target_even

end CenterFrameCertificate
end ExactFourier
end OAI
