import OAI.Computability.FourierCircuit.GlobalFrameSchedule
import OAI.Computability.FourierCircuit.CenterStageTowerTransport

/-!
# Recursive prefix bridge for the frame schedule

`GlobalFrameSchedule.recursiveStage` gives the correct local direction counts
at every finite depth, but its prefix labels are chosen independently at each
depth.  This file supplies the missing algebraic bridge: a tower-backed stage
uses one recursively inserted prefix label, and the next full-address label is
obtained from the previous one by the isometric `tensorLift`.

The result is still an abstract frame interface.  It does not assert that the
tensor-lift permutation is a legal complex gate sequence or give a global gate
count; those obligations remain explicit for the eventual circuit theorem.
-/

namespace OAI
namespace ExactFourier
namespace GlobalFrameTowerBridge

open GlobalFrameSchedule
open CenterStageTowerTransport
open StagePrefixLabelAudit
open StagePrefixAudit

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-! ## A tower-backed stage -/

noncomputable def towerBackedStage {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) : GeneralStageFrame (TowerPrefix h k) h :=
  GeneralStageFrame.mkCertified
    (towerPrefix h p0 a k)
    (a k) (a (k + 1))
    (towerPrefix_unit h p0 a hp0 ha k)
    (ha k) (ha (k + 1)) (haa k) hh

theorem towerBackedStage_counts {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    centreCount (towerBackedStage hh p0 a hp0 ha haa k) = h ∧
      sideCount (towerBackedStage hh p0 a hp0 ha haa k) = h - 2 := by
  constructor
  · simpa [centreCount] using
      (towerBackedStage hh p0 a hp0 ha haa k).centre_directions
  · simpa [sideCount] using
      (towerBackedStage hh p0 a hp0 ha haa k).side_directions

theorem towerBackedStage_transition {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    (towerBackedStage hh p0 a hp0 ha haa k).target =
      (towerBackedStage hh p0 a hp0 ha haa (k + 1)).source := by
  rfl

/-! ## Full-address transport -/

theorem towerBackedStage_label_transport {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    tensorLift (a (k + 1))
        (towerLabel h p0 a k) =
      towerLabel h p0 a (k + 1) := by
  exact towerTransition p0 a k

theorem towerBackedStage_embedded_unit {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    dotProduct
        (towerLabel h p0 a k)
        (towerLabel h p0 a k) = (1 : F) := by
  change dotProduct
      (embeddedLabel (towerPrefix h p0 a k) (a k))
      (embeddedLabel (towerPrefix h p0 a k) (a k)) = (1 : F)
  exact (towerBackedStage hh p0 a hp0 ha haa k).source_embedded_unit

theorem towerBackedStage_embedded_orthogonal {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    dotProduct
        (towerLabel h p0 a k)
        (embeddedLabel (towerPrefix h p0 a k) (a (k + 1))) = (0 : F) := by
  change dotProduct
      (embeddedLabel (towerPrefix h p0 a k) (a k))
      (embeddedLabel (towerPrefix h p0 a k) (a (k + 1))) = (0 : F)
  exact (towerBackedStage hh p0 a hp0 ha haa k).embedded_labels_orthogonal

/-! ## Direction totals for any finite tower prefix -/

theorem towerBackedStage_total_direction_count {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (n : ℕ) :
    (∑ k ∈ Finset.range n,
      centreCount (towerBackedStage hh p0 a hp0 ha haa k)) = n * h ∧
    (∑ k ∈ Finset.range n,
      sideCount (towerBackedStage hh p0 a hp0 ha haa k)) = n * (h - 2) := by
  have hc : ∀ k, centreCount (towerBackedStage hh p0 a hp0 ha haa k) = h :=
    fun k => (towerBackedStage hh p0 a hp0 ha haa k).centre_directions
  have hs : ∀ k, sideCount (towerBackedStage hh p0 a hp0 ha haa k) = h - 2 :=
    fun k => (towerBackedStage hh p0 a hp0 ha haa k).side_directions
  constructor
  · simp [hc]
  · simp [hs]

/-! ## Concrete h = 24 alternating tower interface -/

noncomputable def h24TowerPrefix : PrefixLabel 24 0 :=
  prefixUnit (ι := TowerPrefix 24 0) (PUnit.unit)

noncomputable def h24TowerActive (k : ℕ) : Active 24 :=
  if Even k then stageX (by norm_num) else stageY (by norm_num)

theorem h24TowerPrefix_unit :
    dotProduct h24TowerPrefix h24TowerPrefix = (1 : F) := by
  exact prefixUnit_unit (ι := TowerPrefix 24 0) PUnit.unit

theorem h24TowerActive_unit (k : ℕ) :
    dotProduct (h24TowerActive k) (h24TowerActive k) = (1 : F) := by
  by_cases hk : Even k
  · rw [h24TowerActive, if_pos hk]
    exact xLabel_unit (h := 24) (by norm_num)
  · rw [h24TowerActive, if_neg hk]
    exact yLabel_unit (h := 24) (by norm_num)

theorem h24TowerActive_orthogonal (k : ℕ) :
    dotProduct (h24TowerActive k) (h24TowerActive (k + 1)) = (0 : F) := by
  by_cases hk : Even k
  · have hnext : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr hk.add_one
    rw [h24TowerActive, if_pos hk, h24TowerActive, if_neg hnext]
    exact labels_orthogonal (h := 24) (by norm_num)
  · have hnext : Even (k + 1) := (Nat.not_even_iff_odd.mp hk).add_one
    rw [h24TowerActive, if_neg hk, h24TowerActive, if_pos hnext]
    rw [dotProduct_comm]
    exact labels_orthogonal (h := 24) (by norm_num)

theorem h24_tower_interface (k : ℕ) :
    centreCount
        (towerBackedStage (h := 24) (by norm_num)
          h24TowerPrefix h24TowerActive h24TowerPrefix_unit
          h24TowerActive_unit h24TowerActive_orthogonal k) = 24 ∧
      sideCount
        (towerBackedStage (h := 24) (by norm_num)
          h24TowerPrefix h24TowerActive h24TowerPrefix_unit
          h24TowerActive_unit h24TowerActive_orthogonal k) = 22 ∧
      dotProduct
          (towerLabel 24 h24TowerPrefix h24TowerActive k)
          (embeddedLabel
            (towerPrefix 24 h24TowerPrefix h24TowerActive k)
            (h24TowerActive (k + 1))) = (0 : F) ∧
      tensorLift (h24TowerActive (k + 1))
          (towerLabel 24 h24TowerPrefix h24TowerActive k) =
        towerLabel 24 h24TowerPrefix h24TowerActive (k + 1) := by
  have hc := towerBackedStage_counts (h := 24) (by norm_num)
    h24TowerPrefix h24TowerActive h24TowerPrefix_unit
    h24TowerActive_unit h24TowerActive_orthogonal k
  exact ⟨hc.1, by simpa using hc.2,
    towerBackedStage_embedded_orthogonal (h := 24) (by norm_num)
      h24TowerPrefix h24TowerActive h24TowerPrefix_unit
      h24TowerActive_unit h24TowerActive_orthogonal k,
    towerBackedStage_label_transport (h := 24) (by norm_num)
      h24TowerPrefix h24TowerActive h24TowerPrefix_unit
      h24TowerActive_unit h24TowerActive_orthogonal k⟩

/-! ## Reindexing the tower into the concrete `Fin (h^k)` addresses -/

noncomputable def reindexedPrefix {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) : Fin (h ^ k) → F :=
  prefixReindex (towerPrefixProductFinEquiv h k)
    (towerPrefix h p0 a k)

theorem reindexedPrefix_unit {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F)) (k : ℕ) :
    dotProduct (reindexedPrefix p0 a k) (reindexedPrefix p0 a k) = (1 : F) := by
  rw [reindexedPrefix, prefixReindex_dot]
  exact towerPrefix_unit h p0 a hp0 ha k

noncomputable def reindexedStage {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) : GeneralStageFrame (Fin (h ^ k)) h :=
  GeneralStageFrame.mkCertified
    (reindexedPrefix p0 a k)
    (a k) (a (k + 1))
    (reindexedPrefix_unit p0 a hp0 ha k)
    (ha k) (ha (k + 1)) (haa k) hh

theorem reindexedStage_counts {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    centreCount (reindexedStage hh p0 a hp0 ha haa k) = h ∧
      sideCount (reindexedStage hh p0 a hp0 ha haa k) = h - 2 := by
  constructor
  · simpa [centreCount] using
      (reindexedStage hh p0 a hp0 ha haa k).centre_directions
  · simpa [sideCount] using
      (reindexedStage hh p0 a hp0 ha haa k).side_directions

theorem addressReindex_left_inverse {α β : Type*} {h : ℕ}
    (e : α ≃ β) (v : α × Fin h → F) :
    addressReindex e.symm (addressReindex e v) = v := by
  funext z
  rcases z with ⟨x, j⟩
  simp [addressReindex]

theorem addressReindex_right_inverse {α β : Type*} {h : ℕ}
    (e : α ≃ β) (v : β × Fin h → F) :
    addressReindex e (addressReindex e.symm v) = v := by
  funext z
  rcases z with ⟨x, j⟩
  simp [addressReindex]

theorem addressReindex_dot {α β : Type*} {h : ℕ}
    [Fintype α] [Fintype β]
    (e : α ≃ β) (v v' : α × Fin h → F) :
    dotProduct (addressReindex e v) (addressReindex e v') =
      dotProduct v v' := by
  change dotProduct
      (prefixReindex (e.prodCongr (Equiv.refl (Fin h))) v)
      (prefixReindex (e.prodCongr (Equiv.refl (Fin h))) v') = _
  exact prefixReindex_dot (e.prodCongr (Equiv.refl (Fin h))) v v'

theorem reindexedLabel_transport {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) :
    addressReindex (towerPrefixProductFinEquiv h k)
        (towerLabel h p0 a k) =
      embeddedLabel (reindexedPrefix p0 a k) (a k) := by
  exact addressReindex_insert (towerPrefixProductFinEquiv h k)
    (towerPrefix h p0 a k) (a k)

theorem reindexedEmbedded_transport {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) (b : Active h) :
    addressReindex (towerPrefixProductFinEquiv h k)
        (embeddedLabel (towerPrefix h p0 a k) b) =
      embeddedLabel (reindexedPrefix p0 a k) b := by
  exact addressReindex_insert (towerPrefixProductFinEquiv h k)
    (towerPrefix h p0 a k) b

noncomputable def finTowerLift {h k : ℕ} (q : Active h)
    (v : Fin (h ^ k) × Fin h → F) :
    Fin (h ^ (k + 1)) × Fin h → F :=
  addressReindex (towerPrefixProductFinEquiv h (k + 1))
    (tensorLift q
      (addressReindex (towerPrefixProductFinEquiv h k).symm v))

theorem finTowerLift_source {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) :
    finTowerLift (a (k + 1))
        (embeddedLabel (reindexedPrefix p0 a k) (a k)) =
      embeddedLabel (reindexedPrefix p0 a (k + 1)) (a (k + 1)) := by
  rw [← reindexedLabel_transport p0 a k,
    ← reindexedLabel_transport p0 a (k + 1)]
  unfold finTowerLift
  rw [addressReindex_left_inverse]
  rw [towerTransition]

theorem finTowerLift_dot_of_unit {h k : ℕ} (q : Active h)
    (hq : dotProduct q q = (1 : F))
    (v v' : Fin (h ^ k) × Fin h → F) :
    dotProduct (finTowerLift q v) (finTowerLift q v') =
      dotProduct v v' := by
  unfold finTowerLift
  rw [addressReindex_dot]
  rw [tensorLift_dot_of_unit q hq]
  rw [addressReindex_dot]

theorem reindexed_stage_interface {h : ℕ} (hh : 2 ≤ h)
    (p0 : PrefixLabel h 0) (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F))
    (k : ℕ) :
    centreCount (reindexedStage hh p0 a hp0 ha haa k) = h ∧
      sideCount (reindexedStage hh p0 a hp0 ha haa k) = h - 2 ∧
      dotProduct
          (embeddedLabel (reindexedPrefix p0 a k) (a k))
          (embeddedLabel (reindexedPrefix p0 a k) (a (k + 1))) = (0 : F) ∧
      finTowerLift (a (k + 1))
          (embeddedLabel (reindexedPrefix p0 a k) (a k)) =
        embeddedLabel (reindexedPrefix p0 a (k + 1)) (a (k + 1)) := by
  have hc := reindexedStage_counts hh p0 a hp0 ha haa k
  have ho : dotProduct
      (embeddedLabel (reindexedPrefix p0 a k) (a k))
      (embeddedLabel (reindexedPrefix p0 a k) (a (k + 1))) = (0 : F) := by
    rw [← reindexedEmbedded_transport p0 a k (a k)]
    rw [← reindexedEmbedded_transport p0 a k (a (k + 1))]
    rw [addressReindex_dot]
    exact (towerBackedStage hh p0 a hp0 ha haa k).embedded_labels_orthogonal
  exact ⟨hc.1, hc.2, ho, finTowerLift_source p0 a k⟩

end GlobalFrameTowerBridge
end ExactFourier
end OAI
