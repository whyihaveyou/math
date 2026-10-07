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
open PairTargetFrameLocal


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

/-- Reindexing sends a binary indicator to the indicator of the permuted set. -/
theorem activeReindex_indicator {h : ℕ} (e : Fin h ≃ Fin h)
    (T : Finset (Fin h)) :
    activeReindex e (indicator T) = indicator (T.image e) := by
  funext i
  by_cases hi : e.symm i ∈ T
  · have him : i ∈ T.image e :=
      Finset.mem_image.mpr ⟨e.symm i, hi, e.apply_symm_apply i⟩
    simp [activeReindex, indicator, hi, him]
  · have him : i ∉ T.image e := by
      intro him
      rcases Finset.mem_image.mp him with ⟨a, ha, heq⟩
      have hae : a = e.symm i := by
        apply e.injective
        simpa using heq
      exact hi (hae ▸ ha)
    simp [activeReindex, indicator, hi, him]

@[simp] theorem activeReindex_pairLabel {h : ℕ} (e : Fin h ≃ Fin h)
    (F : Finset (Fin h)) (j : PairIndex F) :
    activeReindex e (pairLabel F j) =
      indicator ((insert j.val F).image e) := by
  exact activeReindex_indicator e (insert j.val F)

/-- Exact transport of the A-bank pair span under an active-label permutation. -/
theorem activeReindex_pairSpan_eq {h : ℕ} (e : Fin h ≃ Fin h)
    (F : Finset (Fin h)) :
    Submodule.map (activeReindex e).toLinearMap (pairSpan F) =
      pairSpan (F.image e) := by
  rw [pairSpan, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
    let j' : PairIndex (F.image e) :=
      ⟨e j.val, by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨a, ha, heq⟩
        have hae : a = j.val := by
          apply e.injective
          simpa using heq
        exact j.property (hae ▸ ha)⟩
    refine ⟨j', ?_⟩
    change indicator (insert j'.val (F.image e)) =
      activeReindex e (indicator (insert j.val F))
    rw [activeReindex_indicator]
    simp [j']
  · rintro ⟨j, rfl⟩
    let j' : PairIndex F :=
      ⟨e.symm j.val, by
        intro hmem
        apply j.property
        exact Finset.mem_image.mpr
          ⟨e.symm j.val, hmem, e.apply_symm_apply j.val⟩⟩
    refine ⟨pairLabel F j', ⟨j', rfl⟩, ?_⟩
    change activeReindex e (indicator (insert j'.val F)) =
      indicator (insert j.val (F.image e))
    rw [activeReindex_indicator]
    simp [j']

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
