import OAI.Computability.FourierCircuit.ParityTargetAggregateFrameCandidate
import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.Tactic

/-!
# Global target-boundary obstruction for parity-split aggregates

The local parity split is frame-compatible for a fixed target: both source
banks lie in that target's codimension-one boundary.  This file records the
sharp global limitation.  Across all targets, the intersection of those
boundaries is zero, because triple indicators span the full active factor.
Thus one target-independent active frame cannot contain every parity bank
unless it is the zero space.  Any global construction must therefore route
between target-labelled boundaries (or introduce additional address factors);
this is a linear-algebra no-go, not a circuit lower bound.
-/

namespace OAI
namespace ExactFourier
namespace ParityGlobalBoundaryNoGo

open FrameLabels
open ParityTargetAggregateFrameCandidate
open TripleSpan

abbrev F := ZMod 2
abbrev V := Fin 24 → F

/-- For every `h ≥ 4`, all target boundaries intersect trivially. -/
theorem all_target_boundaries_eq_zero_of_four {h : ℕ} (hh : 4 ≤ h)
    {v : Fin h → F}
    (hv : ∀ S : CenterCompression.Triple h, v ∈ targetBoundary S) :
    v = 0 := by
  let f : (Fin h → F) →ₗ[F] F := dotForm v
  have htriple : ∀ T : Finset (Fin h), T.card = 3 →
      f (indicator T) = 0 := by
    intro T hT
    let S : CenterCompression.Triple h := ⟨T, by
      simp [CenterCompression.tripleSet, hT]⟩
    have hmem := hv S
    rw [targetBoundary, Submodule.orthogonalBilin_span_singleton] at hmem
    have hmem' : dotForm (indicator T) v = 0 := by
      exact hmem
    change dotForm v (indicator T) = 0
    simpa [f, dotForm, dotProduct_comm] using hmem'
  have hspan : TripleSpan h ≤ LinearMap.ker f := by
    apply Submodule.span_le.2
    intro x hx
    rcases hx with ⟨T, hT, rfl⟩
    exact htriple T hT
  have htop : LinearMap.ker f = (⊤ : Submodule F (Fin h → F)) := by
    apply top_unique
    rw [← tripleIndicators_span_eq_top_of_four hh]
    exact hspan
  have hfzero : ∀ x : Fin h → F, f x = 0 := by
    intro x
    have hx : x ∈ LinearMap.ker f := by
      rw [htop]
      trivial
    exact hx
  funext i
  have hi := hfzero (Pi.single i 1)
  change dotProduct v (Pi.single i 1) = 0 at hi
  simpa [dotProduct, Pi.single_apply] using hi

/-- The h=24 instance used by the parity candidate. -/
theorem all_target_boundaries_eq_zero {v : Fin 24 → F}
    (hv : ∀ S : CenterCompression.Triple 24, v ∈ targetBoundary S) :
    v = 0 := by
  exact all_target_boundaries_eq_zero_of_four (h := 24) (by norm_num) hv

end ParityGlobalBoundaryNoGo
end ExactFourier
end OAI
