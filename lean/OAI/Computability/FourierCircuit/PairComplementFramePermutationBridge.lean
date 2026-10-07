import OAI.Computability.FourierCircuit.PairComplementFramePermutation
import OAI.Computability.FourierCircuit.CenterBoundaryTensorLift
import OAI.Computability.FourierCircuit.PairComplementFrameCompatibleCandidate
import Mathlib.Tactic

/-!
# Tensor-side bridge for pair/complement frame permutations

`PairComplementFramePermutation` gives an active-coordinate equivalence which
transports the disjoint-triple bank for `F` to the bank for `F.image e`.
This file lifts that equivalence through a fixed prefix insertion.  The result
is a precise side-wire interface: the lifted map carries the inserted B-bank
submodule to the inserted permuted B-bank submodule and preserves its h=24
rank.  No claim is made that this lift is one legal complex gate, that it
commutes with the scalar pair/complement invocation, or that all permutations
can be scheduled globally.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementFramePermutationBridge

open PairComplementDisjointSpan
open CenterBoundaryTensorLift
open CenterRowGeneral

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] {h : ℕ}

/- The inserted B-bank support inside a fixed prefix fibre. -/
def insertedDisjointBank (p : ι → F) (Fset : Finset (Fin h)) :
    Submodule F (Address ι h) :=
  LinearMap.range ((CenterRowGeneral.insert p).comp
    (disjointTripleSpan Fset).subtype)

noncomputable def liftedReindex (e : Fin h ≃ Fin h) :
    Address ι h ≃ₗ[F] Address ι h :=
  CenterBoundaryTensorLift.lift (activeReindex e)

@[simp] theorem liftedReindex_insert (e : Fin h ≃ Fin h)
    (p : ι → F) (x : Active h) :
    liftedReindex e (CenterRowGeneral.insert p x) =
      CenterRowGeneral.insert p (activeReindex e x) := by
  exact CenterBoundaryTensorLift.lift_insert (activeReindex e) p x

@[simp] theorem activeReindex_symm (e : Fin h ≃ Fin h) :
    (activeReindex e).symm = activeReindex e.symm := by
  ext x i
  rfl

@[simp] theorem liftedReindex_symm (e : Fin h ≃ Fin h) (z : Address ι h) :
    (liftedReindex e).symm z =
      CenterBoundaryTensorLift.lift (activeReindex e).symm z := by
  rfl

theorem lifted_bank_map_le (e : Fin h ≃ Fin h)
    (p : ι → F) (Fset : Finset (Fin h))
    (hF : Fset.card = 2) (hh : 6 ≤ h) :
    Submodule.map (liftedReindex e).toLinearMap
        (insertedDisjointBank p Fset) ≤
      insertedDisjointBank p (Fset.image e) := by
  intro z hz
  rcases Submodule.mem_map.mp hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x, rfl⟩
  refine ⟨⟨activeReindex e x, ?_⟩, ?_⟩
  · have hspan := activeReindex_disjointSpan_eq e Fset
      hF hh
    rw [← hspan]
    exact Submodule.mem_map.mpr ⟨x, x.property, rfl⟩
  · simp [liftedReindex_insert]

theorem lifted_bank_map_eq (e : Fin h ≃ Fin h)
    (p : ι → F) (Fset : Finset (Fin h))
    (hF : Fset.card = 2) (hh : 6 ≤ h) :
    Submodule.map (liftedReindex e).toLinearMap
        (insertedDisjointBank p Fset) =
      insertedDisjointBank p (Fset.image e) := by
  apply le_antisymm
  · exact lifted_bank_map_le e p Fset hF hh
  · intro z hz
    refine Submodule.mem_map.mpr
      ⟨(liftedReindex e).symm z, ?_, (liftedReindex e).apply_symm_apply z⟩
    rcases hz with ⟨x, hzx⟩
    have hspan := activeReindex_disjointSpan_eq e Fset hF hh
    have hxmap : (x : Active h) ∈
        Submodule.map (activeReindex e).toLinearMap (disjointTripleSpan Fset) := by
      rw [hspan]
      exact x.property
    have hxpre : (activeReindex e).symm (x : Active h) ∈
        disjointTripleSpan Fset := by
      rcases Submodule.mem_map.mp hxmap with ⟨y, hy, hxy⟩
      have hy_eq : y = (activeReindex e).symm (x : Active h) := by
        apply (activeReindex e).injective
        exact hxy.trans ((activeReindex e).apply_symm_apply _).symm
      simpa [hy_eq] using hy
    have hz_eq : z = CenterRowGeneral.insert p x := hzx.symm
    rw [hz_eq, liftedReindex_symm, lift_insert]
    exact ⟨⟨(activeReindex e).symm x, hxpre⟩, rfl⟩

/-- The inserted B-bank has exactly the active-bank rank when the prefix
insertion is unit.  This is the rank fact used by the frame-cost ledger. -/
theorem inserted_bank_finrank
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (Fset : Finset (Fin h)) (hF : Fset.card = 2) (hh : 6 ≤ h) :
    Module.finrank F (insertedDisjointBank p Fset) = h - 2 := by
  rw [insertedDisjointBank]
  have hcomp : Function.Injective
      ((CenterRowGeneral.insert p).comp (disjointTripleSpan Fset).subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply CenterRowGeneral.insert_injective p hp
    exact hxy
  rw [LinearMap.finrank_range_of_inj hcomp]
  simpa using (PairComplementDisjointSpan.disjointTripleSpan_finrank Fset hF hh)

namespace H24

/- The h=24 specialization is the side-wire interface used by the pair /
   complement candidate: each transported B-bank remains an exact inserted
   submodule after the active-coordinate permutation. -/
theorem lifted_b_bank_map_eq
    (e : Fin 24 ≃ Fin 24) (p : ι → F) (Fset : Finset (Fin 24))
    (hF : Fset.card = 2) :
    Submodule.map (liftedReindex e).toLinearMap
        (insertedDisjointBank p Fset) =
      insertedDisjointBank p (Fset.image e) := by
  exact lifted_bank_map_eq e p Fset hF (by norm_num)

theorem inserted_b_bank_rank
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (insertedDisjointBank p Fset) = 22 := by
  simpa using inserted_bank_finrank p hp Fset hF (by norm_num)

theorem b_bank_rank_transport
    (e : Fin 24 ≃ Fin 24) (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (Submodule.map (activeReindex e).toLinearMap
      (disjointTripleSpan Fset)) = 22 := by
  exact PairComplementDisjointSpan.H24.activeReindex_disjointSpan_rank_transport
    e Fset hF

theorem b_bank_rank_is_permutation_invariant
    (e : Fin 24 ≃ Fin 24) (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (disjointTripleSpan Fset) =
      Module.finrank F (disjointTripleSpan (Fset.image e)) := by
  rw [PairComplementDisjointSpan.H24.pair_disjointTripleSpan_rank Fset hF,
    PairComplementDisjointSpan.H24.pair_disjointTripleSpan_rank (Fset.image e)]
  rw [Finset.card_image_of_injective Fset e.injective, hF]

end H24

end PairComplementFramePermutationBridge
end ExactFourier
end OAI
