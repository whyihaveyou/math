import OAI.Computability.FourierCircuit.TargetLabelCover
import Mathlib.Tactic
open scoped BigOperators
namespace OAI
namespace ExactFourier
namespace TargetLabelCover
open CenterCompression
open FrameLabels
open ParityTargetAggregateFrameCandidate
def singletonCover {h : ℕ} (C : Finset (Fin h)) : Prop :=
  ∀ S : Triple h, ∃ i ∈ C, i ∉ S.1

lemma exists_triple_superset_of_card_le_three {h : ℕ} (hh : 4 ≤ h)
    (C : Finset (Fin h)) (hC : C.card ≤ 3) :
    ∃ S : Triple h, C ⊆ S.1 := by
  have hthree_univ : 3 ≤ (Finset.univ : Finset (Fin h)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨T, hCT, hT⟩ := Finset.exists_superset_card_eq hC hthree_univ
  have hTmem : T ∈ tripleSet h := by
    simp [tripleSet, hT]
  exact ⟨⟨T, hTmem⟩, hCT⟩

theorem singletonCover_card_ge_four {h : ℕ} (hh : 4 ≤ h)
    (C : Finset (Fin h)) (hcover : singletonCover C) :
    4 ≤ C.card := by
  by_contra hlt
  have hC : C.card ≤ 3 := by omega
  obtain ⟨S, hCS⟩ := exists_triple_superset_of_card_le_three hh C hC
  obtain ⟨i, hiC, hiS⟩ := hcover S
  exact hiS (hCS hiC)

 theorem fourEmbedding_cover {h : ℕ} (hh : 4 ≤ h) :
    singletonCover (Finset.univ.image (fourEmbedding hh)) := by
  intro S
  obtain ⟨i, hi⟩ := exists_fin4_not_mem hh S
  exact ⟨fourEmbedding hh i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩

theorem fourEmbedding_cover_card {h : ℕ} (hh : 4 ≤ h) :
    (Finset.univ.image (fourEmbedding hh)).card = 4 := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    exact (fourEmbedding hh).injective hij

theorem fourEmbedding_cover_minimal {h : ℕ} (hh : 4 ≤ h) :
    4 ≤ (Finset.univ.image (fourEmbedding hh)).card := by
  rw [fourEmbedding_cover_card hh]

end TargetLabelCover
end ExactFourier
end OAI
