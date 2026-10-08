import OAI.Computability.FourierCircuit.ParityTargetAggregateFrameCandidate
import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.Tactic

/-!
# Four singleton labels cover one target boundary

For `h ≥ 4`, fix a target triple `S`.  The four coordinates coming from
`Fin 4 ↪ Fin h` give four distinct singleton (coordinate) labels.  Since `S`
has only three elements, at least one of those four labels has its coordinate
outside `S`; its dot product with the target indicator is therefore zero, so it
lies in the target boundary.

This is a finite label-routing witness.  It says that a target line can be
assigned one legal label among four explicitly embedded singleton frames.  It
does not construct source aggregates, scalar commutations, a gate realization,
or a global schedule, and it gives no circuit-cost bound by itself.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace TargetLabelCover

open CenterCompression
open FrameLabels
open ParityTargetAggregateFrameCandidate

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- The canonical inclusion of four active coordinates into `Fin h`. -/
def fourEmbedding {h : ℕ} (hh : 4 ≤ h) : Fin 4 ↪ Fin h :=
  Fin.castLEEmb hh

/-- The four singleton active labels associated with that inclusion. -/
def singletonLabel {h : ℕ} (hh : 4 ≤ h) (i : Fin 4) : Active h :=
  TripleSpan.basisVec (fourEmbedding hh i)

@[simp] theorem singletonLabel_apply_eq {h : ℕ} (hh : 4 ≤ h)
    (i : Fin 4) : singletonLabel hh i = TripleSpan.basisVec (fourEmbedding hh i) := rfl

/-- A singleton label is a unit vector for the binary dot form. -/
theorem singletonLabel_unit {h : ℕ} (hh : 4 ≤ h) (i : Fin 4) :
    dotForm (singletonLabel hh i) (singletonLabel hh i) = (1 : F) := by
  change dotProduct (Pi.single (fourEmbedding hh i) 1)
    (Pi.single (fourEmbedding hh i) 1) = 1
  rw [Matrix.dotProduct_single_one]
  simp

/-- Distinct embedded singleton labels are orthogonal. -/
theorem singletonLabel_orthogonal {h : ℕ} (hh : 4 ≤ h)
    {i j : Fin 4} (hij : i ≠ j) :
    dotForm (singletonLabel hh i) (singletonLabel hh j) = (0 : F) := by
  have hval : fourEmbedding hh i ≠ fourEmbedding hh j := by
    intro hval
    exact hij ((fourEmbedding hh).injective hval)
  change dotProduct (Pi.single (fourEmbedding hh i) 1)
    (Pi.single (fourEmbedding hh j) 1) = 0
  rw [Matrix.dotProduct_single_one]
  simp [hval]

/-- The four labels are pairwise distinct. -/
theorem singletonLabel_injective {h : ℕ} (hh : 4 ≤ h) :
    Function.Injective (singletonLabel hh) := by
  intro i j hij
  by_contra hne
  have hval : fourEmbedding hh i ≠ fourEmbedding hh j := by
    intro hval
    exact hne ((fourEmbedding hh).injective hval)
  have hcoord := congrFun hij (fourEmbedding hh i)
  simp [singletonLabel, TripleSpan.basisVec, hval] at hcoord

/-- At least one of the four embedded coordinates is outside a target triple. -/
theorem exists_fin4_not_mem {h : ℕ} (hh : 4 ≤ h) (S : Triple h) :
    ∃ i : Fin 4, fourEmbedding hh i ∉ S.1 := by
  by_contra hnone
  push_neg at hnone
  have himage : Finset.univ.image (fourEmbedding hh) ⊆ S.1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hnone i
  have hcard_le : (Finset.univ.image (fourEmbedding hh)).card ≤ S.1.card :=
    Finset.card_le_card himage
  have hcard_image : (Finset.univ.image (fourEmbedding hh)).card = 4 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i hi j hj hij
      exact (fourEmbedding hh).injective hij
  rw [hcard_image, CenterCompression.triple_card S] at hcard_le
  omega

/-- A singleton coordinate outside `S` lies in the target boundary. -/
theorem singletonLabel_mem_targetBoundary_of_not_mem {h : ℕ}
    (hh : 4 ≤ h) (S : Triple h) (i : Fin 4)
    (hi : fourEmbedding hh i ∉ S.1) :
    singletonLabel hh i ∈ targetBoundary S := by
  rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
  change dotForm (indicator S.1) (singletonLabel hh i) = 0
  simp [singletonLabel, TripleSpan.basisVec, dotForm, dotProduct, indicator, hi]

/-- The four-frame cover hits the target boundary. -/
theorem exists_singletonLabel_mem_targetBoundary {h : ℕ}
    (hh : 4 ≤ h) (S : Triple h) :
    ∃ i : Fin 4, singletonLabel hh i ∈ targetBoundary S := by
  obtain ⟨i, hi⟩ := exists_fin4_not_mem hh S
  exact ⟨i, singletonLabel_mem_targetBoundary_of_not_mem hh S i hi⟩

/-- The complete finite witness carried by the four singleton frames.

`target_hit` is existential: it identifies a legal target-boundary label among
the four frames.  The structure intentionally records no physical gate or
schedule field; those obligations remain outside this label certificate.
-/
structure FourFrameTargetRoutingWitness (h : ℕ) (S : Triple h)
    (hh : 4 ≤ h) where
  labels : Fin 4 → Active h
  labels_eq : labels = singletonLabel hh
  labels_injective : Function.Injective labels
  labels_unit : ∀ i, dotForm (labels i) (labels i) = (1 : F)
  target_hit : ∃ i, labels i ∈ targetBoundary S

/-- Construct the four-frame target-routing witness for every target triple. -/
def fourFrameTargetRoutingWitness {h : ℕ} (hh : 4 ≤ h) (S : Triple h) :
    FourFrameTargetRoutingWitness h S hh where
  labels := singletonLabel hh
  labels_eq := rfl
  labels_injective := singletonLabel_injective hh
  labels_unit := singletonLabel_unit hh
  target_hit := exists_singletonLabel_mem_targetBoundary hh S

@[simp] theorem fourFrameTargetRoutingWitness_card {h : ℕ}
    (hh : 4 ≤ h) (S : Triple h) :
    Fintype.card (Fin 4) = 4 := by
  simp

/-- The witness exposes the exact target-routing statement without adding a
physical schedule assumption. -/
theorem fourFrame_target_hit {h : ℕ} (hh : 4 ≤ h) (S : Triple h) :
    ∃ W : FourFrameTargetRoutingWitness h S hh,
      ∃ i : Fin 4, W.labels i ∈ targetBoundary S := by
  refine ⟨fourFrameTargetRoutingWitness hh S, ?_⟩
  exact (fourFrameTargetRoutingWitness hh S).target_hit

end TargetLabelCover
end ExactFourier
end OAI
