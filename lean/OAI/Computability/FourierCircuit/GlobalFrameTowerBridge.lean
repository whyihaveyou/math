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

end GlobalFrameTowerBridge
end ExactFourier
end OAI
