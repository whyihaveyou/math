import OAI.Computability.FourierCircuit.PairComplementDisjointSpan

/-!
# Active-label permutation transport for the disjoint-triple pair bank

The pair-complement bank is defined by vanishing on a fixed active pair `F`.
This file proves that a permutation of active labels transports the bank to the
correspondingly permuted pair.  It is still a label-space statement: it does
not assert that the permutation is one legal complex gate or that all such
transports fit into one global circuit schedule.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementDisjointSpan

open FrameLabels


/-- Reindex active coordinates by a permutation of `Fin h`. -/
noncomputable def activeReindex {h : ℕ} (e : Fin h ≃ Fin h) :
    V h ≃ₗ[K] V h where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp
  map_smul' a x := by
    funext i
    simp

@[simp] theorem activeReindex_apply {h : ℕ} (e : Fin h ≃ Fin h)
    (x : V h) (i : Fin h) : activeReindex e x i = x (e.symm i) := rfl

/-- The coordinate submodule complementary to `F` maps into the complementary
submodule of the permuted pair. -/
theorem activeReindex_away_le {h : ℕ} (e : Fin h ≃ Fin h)
    (F : Finset (Fin h)) :
    Submodule.map (activeReindex e).toLinearMap (awaySubmodule F) ≤
      awaySubmodule (F.image e) := by
  intro x hx
  rcases (Submodule.mem_map.mp hx) with ⟨y, hy, rfl⟩
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  simpa [activeReindex] using hy j hj

/-- The complementary submodule is transported exactly, using the inverse
permutation for the reverse inclusion. -/
theorem activeReindex_away_eq {h : ℕ} (e : Fin h ≃ Fin h)
    (F : Finset (Fin h)) :
    Submodule.map (activeReindex e).toLinearMap (awaySubmodule F) =
      awaySubmodule (F.image e) := by
  apply le_antisymm
  · exact activeReindex_away_le e F
  · intro x hx
    have hx' : activeReindex e.symm x ∈ awaySubmodule F := by
      intro j hj
      have hje : e j ∈ F.image e :=
        Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have hzero := hx (e j) hje
      simpa [activeReindex] using hzero
    refine Submodule.mem_map.mpr ⟨activeReindex e.symm x, hx', ?_⟩
    simpa [activeReindex]

/-- Exact transport of the disjoint-triple span under an active-label
permutation.  The rank hypothesis is preserved because equivalences are
injective and `Finset.image` preserves cardinality. -/
theorem activeReindex_disjointSpan_eq {h : ℕ} (e : Fin h ≃ Fin h)
    (F : Finset (Fin h)) (hF : F.card = 2) (hh : 6 ≤ h) :
    Submodule.map (activeReindex e).toLinearMap (disjointTripleSpan F) =
      disjointTripleSpan (F.image e) := by
  have hFi : (F.image e).card = 2 := by
    rw [Finset.card_image_of_injective F e.injective, hF]
  rw [disjointTripleSpan_eq_awaySubmodule F hF hh,
    disjointTripleSpan_eq_awaySubmodule (F.image e) hFi hh]
  exact activeReindex_away_eq e F

namespace H24

theorem activeReindex_disjointSpan_rank_transport (e : Fin 24 ≃ Fin 24)
    (F : Finset (Fin 24)) (hF : F.card = 2) :
    Module.finrank K
        (Submodule.map (activeReindex e).toLinearMap (disjointTripleSpan F)) = 22 := by
  rw [activeReindex_disjointSpan_eq e F hF (by norm_num)]
  exact pair_disjointTripleSpan_rank (F.image e) (by
    rw [Finset.card_image_of_injective F e.injective, hF])

end H24
end PairComplementDisjointSpan
end ExactFourier
end OAI
