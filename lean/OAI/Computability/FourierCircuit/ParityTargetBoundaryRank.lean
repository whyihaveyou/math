import OAI.Computability.FourierCircuit.ParityTargetAggregateFrameCandidate
import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Rank of the h=24 target boundary

For the fixed target `S = {0,1,2}`, this file proves that the binary target
boundary used by the parity candidate has dimension `24 - 1 = 23`.  The proof
is rank-nullity for the nonzero functional `dotForm (indicator S)`; it does
not identify either parity-source span with the full boundary.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace ParityTargetBoundaryRank

open FrameLabels
open ParityTargetAggregateFrameCandidate

abbrev K := ZMod 2
abbrev V := Fin 24 → K

def target : Finset (Fin 24) := {0, 1, 2}

def boundary : Submodule K V := targetBoundary ⟨target, by native_decide⟩

private theorem basis_zero_indicator :
    TripleSpan.basisVec (0 : Fin 24) = indicator ({0} : Finset (Fin 24)) := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [TripleSpan.basisVec, indicator]
  · simp [TripleSpan.basisVec, indicator, hi]

private theorem target_functional_surjective :
    Function.Surjective
      (dotForm (indicator target) : V →ₗ[K] K) := by
  intro z
  refine ⟨z • TripleSpan.basisVec (0 : Fin 24), ?_⟩
  change dotForm (indicator target) (z • TripleSpan.basisVec (0 : Fin 24)) = z
  rw [map_smul]
  rw [basis_zero_indicator, indicator_dot]
  have hinter : target ∩ ({0} : Finset (Fin 24)) = ({0} : Finset (Fin 24)) := by
    ext i
    simp [target]
  rw [hinter]
  norm_num

private theorem boundary_eq_kernel :
    boundary = LinearMap.ker (dotForm (indicator target) : V →ₗ[K] K) := by
  ext x
  rw [boundary, targetBoundary, Submodule.orthogonalBilin_span_singleton]

theorem boundary_finrank : Module.finrank K boundary = 23 := by
  rw [boundary_eq_kernel]
  let f : V →ₗ[K] K := dotForm (indicator target)
  have hsurj : Function.Surjective f := target_functional_surjective
  have hrange : LinearMap.range f = (⊤ : Submodule K K) :=
    LinearMap.range_eq_top.mpr hsurj
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hrank
  have hdim : Module.finrank K V = 24 := by
    exact Module.finrank_fin_fun K
  rw [hdim] at hrank
  have hker : 1 + Module.finrank K (LinearMap.ker f) = 24 := by
    simpa using hrank
  dsimp [f] at hker
  omega

end ParityTargetBoundaryRank
end ExactFourier
end OAI
