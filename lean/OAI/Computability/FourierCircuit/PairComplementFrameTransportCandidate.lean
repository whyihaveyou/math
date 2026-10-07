import OAI.Computability.FourierCircuit.PairComplementFramePermutationBridge
import OAI.Computability.FourierCircuit.PairComplementFrameCompatibleCandidate
import Mathlib.Tactic

/-!
# High-level frame-transport premise for the pair/complement candidate

The lower-level permutation file proves active-bank transport, and the tensor
bridge lifts it through a fixed prefix insertion.  This file packages those
facts together with the existing h=24 rank/ledger certificate so a later
physical-gate proof can consume one explicit premise.  The package remains
conditional: it does not claim a complex gate implementation, scalar/gate
commutation, or a global all-prefix schedule.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementFrameTransportCandidate

open PairComplementDisjointSpan
open PairTargetFrameLocal
open PairComplementFrameCompatibleCandidate
open PairComplementFramePermutationBridge

abbrev F := ZMod 2

/-- Exact active- and tensor-level B-bank transport for all h=24 pairs and
unit prefixes of the first-prefix type. -/
def H24TransportPremise : Prop :=
  ∀ (e : Fin 24 ≃ Fin 24) (Fset : Finset (Fin 24)),
    Fset.card = 2 →
      Submodule.map (activeReindex e).toLinearMap
          (disjointTripleSpan Fset) = disjointTripleSpan (Fset.image e) ∧
      Submodule.map (activeReindex e).toLinearMap
          (pairSpan Fset) = pairSpan (Fset.image e) ∧
      ∀ (p : Fin 1 → F),
        dotProduct p p = (1 : F) →
          (Submodule.map (liftedReindex (ι := Fin 1) e).toLinearMap
              (insertedDisjointBank p Fset) =
            insertedDisjointBank p (Fset.image e) ∧
           Submodule.map (liftedReindex (ι := Fin 1) e).toLinearMap
              (insertedPairBank p Fset) =
            insertedPairBank p (Fset.image e))

/-- The transport premise is discharged by the active and tensor bridge
certificates. -/
theorem h24_transport_premise : H24TransportPremise := by
  intro e Fset hF
  refine ⟨activeReindex_disjointSpan_eq e Fset hF (by norm_num),
    activeReindex_pairSpan_eq e Fset, ?_⟩
  intro p hp
  exact ⟨PairComplementFramePermutationBridge.H24.lifted_b_bank_map_eq e p Fset hF,
    PairComplementFramePermutationBridge.H24.lifted_pair_bank_map_h24 e p Fset hF⟩

/-- The transported tensor bank keeps the rank used in the aggregate ledger. -/
theorem h24_inserted_bank_rank
    (p : Fin 1 → F) (hp : dotProduct p p = (1 : F))
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (insertedDisjointBank p Fset) = 22 := by
  exact PairComplementFramePermutationBridge.H24.inserted_b_bank_rank p hp Fset hF

theorem h24_inserted_pair_bank_rank
    (p : Fin 1 → F) (hp : dotProduct p p = (1 : F))
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (insertedPairBank p Fset) = 22 := by
  exact PairComplementFramePermutationBridge.H24.inserted_a_bank_rank p hp Fset hF

/-- A single premise combining the already-proved integer ledger with the new
frame-transport facts. -/
def H24FrameCompatibleLedgerWithTransport : Prop :=
  PairComplementFrameCompatibleCandidate.H24.FrameCompatibleLedgerPremise ∧
  H24TransportPremise

theorem h24_frameCompatibleLedgerWithTransport :
    H24FrameCompatibleLedgerWithTransport := by
  exact ⟨PairComplementFrameCompatibleCandidate.H24.frameCompatibleLedgerPremise_arithmetic,
    h24_transport_premise⟩

end PairComplementFrameTransportCandidate
end ExactFourier
end OAI
