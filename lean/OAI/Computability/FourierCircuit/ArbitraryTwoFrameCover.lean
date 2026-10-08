import OAI.Computability.FourierCircuit.TargetLabelCover
import OAI.Computability.FourierCircuit.ParityGlobalBoundaryNoGo
import Mathlib.Tactic

open scoped BigOperators
namespace OAI
namespace ExactFourier
namespace ArbitraryTwoFrameCover

/-!
# A two-label cover using an arbitrary dense binary unit label

For even `h ≥ 4`, let `u = e₀` and `w = 1 + e₀`, the all-ones vector with
its zero coordinate removed.  Both labels are unit and mutually orthogonal.
For every weight-three target exactly one of `u` and `w` is orthogonal to the
target indicator, so this gives a two-frame target-boundary cover when dense
(non-singleton) labels are allowed.  The construction is deliberately separate
from the four-singleton cover: `w` has weight `h - 1`.

The final no-single-label theorem reuses the triple-span rank certificate: no
nonzero target-independent active label can lie in every target boundary.
Nothing here constructs source formation, gates, a global schedule, or a DFT
recurrence; all claims are finite binary-label facts.
-/

open CenterCompression
open FrameLabels
open ParityTargetAggregateFrameCandidate
open ParityGlobalBoundaryNoGo

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

def zeroIndex {h : ℕ} (hh : 1 ≤ h) : Fin h := ⟨0, by omega⟩

def unitLabel {h : ℕ} (hh : 1 ≤ h) : Active h :=
  TripleSpan.basisVec (zeroIndex hh)

def allOnes {h : ℕ} : Active h := fun _ => 1

def denseComplementLabel {h : ℕ} (hh : 1 ≤ h) : Active h :=
  allOnes + unitLabel hh

theorem unitLabel_unit {h : ℕ} (hh : 1 ≤ h) :
    dotForm (unitLabel hh) (unitLabel hh) = (1 : F) := by
  change dotProduct (Pi.single (zeroIndex hh) 1) (Pi.single (zeroIndex hh) 1) = 1
  rw [dotProduct_single_one]
  simp

theorem allOnes_dot_allOnes {h : ℕ} :
    dotForm (allOnes (h := h)) (allOnes (h := h)) = (h : F) := by
  simp [allOnes, dotForm, dotProduct]

theorem allOnes_dot_unit {h : ℕ} (hh : 1 ≤ h) :
    dotForm (allOnes (h := h)) (unitLabel hh) = (1 : F) := by
  simp [allOnes, unitLabel, zeroIndex, TripleSpan.basisVec, dotForm, dotProduct]

theorem unit_dot_allOnes {h : ℕ} (hh : 1 ≤ h) :
    dotForm (unitLabel hh) (allOnes (h := h)) = (1 : F) := by
  simp [allOnes, unitLabel, zeroIndex, TripleSpan.basisVec, dotForm, dotProduct]

theorem denseComplementLabel_unit {h : ℕ} (hh : 2 ≤ h)
    (heven : Even h) :
    dotForm (denseComplementLabel (h := h) (by omega))
      (denseComplementLabel (h := h) (by omega)) = (1 : F) := by
  unfold denseComplementLabel
  change dotProduct (allOnes + unitLabel (by omega : 1 ≤ h))
    (allOnes + unitLabel (by omega : 1 ≤ h)) = 1
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  have hAA := allOnes_dot_allOnes (h := h)
  change dotProduct (allOnes (h := h)) (allOnes (h := h)) = (h : F) at hAA
  have hAU := allOnes_dot_unit (by omega : 1 ≤ h)
  change dotProduct (allOnes (h := h))
      (unitLabel (by omega : 1 ≤ h)) = (1 : F) at hAU
  have hUA := unit_dot_allOnes (by omega : 1 ≤ h)
  change dotProduct (unitLabel (by omega : 1 ≤ h))
      (allOnes (h := h)) = (1 : F) at hUA
  have hUU := unitLabel_unit (by omega : 1 ≤ h)
  change dotProduct (unitLabel (by omega : 1 ≤ h))
      (unitLabel (by omega : 1 ≤ h)) = (1 : F) at hUU
  rw [hAA, hAU, hUA, hUU]
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  have hkk : (k : F) + k = 0 := by
    calc
      (k : F) + k = (2 : F) * k := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hone : (1 : F) + 1 = 0 := by
    calc
      (1 : F) + 1 = (2 : F) := by norm_num
      _ = 0 := htwo
  rw [Nat.cast_add, hkk, hone]
  simp

theorem unit_denseComplementLabel_orthogonal {h : ℕ} (hh : 2 ≤ h) :
    dotForm (unitLabel (by omega : 1 ≤ h))
      (denseComplementLabel (h := h) (by omega)) = (0 : F) := by
  unfold denseComplementLabel
  change dotProduct (unitLabel (by omega : 1 ≤ h))
    (allOnes + unitLabel (by omega : 1 ≤ h)) = 0
  rw [dotProduct_add]
  have hUA := unit_dot_allOnes (by omega : 1 ≤ h)
  change dotProduct (unitLabel (by omega : 1 ≤ h))
      (allOnes (h := h)) = (1 : F) at hUA
  have hUU := unitLabel_unit (by omega : 1 ≤ h)
  change dotProduct (unitLabel (by omega : 1 ≤ h))
      (unitLabel (by omega : 1 ≤ h)) = (1 : F) at hUU
  rw [hUA, hUU]
  have hone : (1 : F) + 1 = 0 := by
    exact CharP.cast_eq_zero (ZMod 2) 2
  rw [hone]

theorem denseComplementLabel_unit_orthogonal {h : ℕ} (hh : 2 ≤ h) :
    dotForm (denseComplementLabel (h := h) (by omega))
      (unitLabel (by omega : 1 ≤ h)) = (0 : F) := by
  change dotProduct (allOnes + unitLabel (by omega : 1 ≤ h))
    (unitLabel (by omega : 1 ≤ h)) = 0
  rw [add_dotProduct]
  have hAU := allOnes_dot_unit (by omega : 1 ≤ h)
  change dotProduct (allOnes (h := h))
      (unitLabel (by omega : 1 ≤ h)) = (1 : F) at hAU
  have hUU := unitLabel_unit (by omega : 1 ≤ h)
  change dotProduct (unitLabel (by omega : 1 ≤ h))
      (unitLabel (by omega : 1 ≤ h)) = (1 : F) at hUU
  rw [hAU, hUU]
  have hone : (1 : F) + 1 = 0 := by
    exact CharP.cast_eq_zero (ZMod 2) 2
  rw [hone]

lemma target_dot_unit {h : ℕ} (hh : 1 ≤ h) (S : Triple h) :
    dotForm (indicator S.1) (unitLabel hh) =
      if zeroIndex hh ∈ S.1 then (1 : F) else 0 := by
  change dotProduct (indicator S.1) (Pi.single (zeroIndex hh) 1) = _
  simp [dotProduct, indicator]

lemma target_dot_dense_of_mem {h : ℕ} (hh : 1 ≤ h) (S : Triple h)
    (hz : zeroIndex hh ∈ S.1) :
    dotForm (indicator S.1)
      (denseComplementLabel (h := h) hh) = (0 : F) := by
  unfold denseComplementLabel
  change dotProduct (indicator S.1)
    (allOnes + unitLabel hh) = 0
  rw [dotProduct_add]
  have hTU := target_dot_unit hh S
  change dotProduct (indicator S.1) (unitLabel hh) =
      if zeroIndex hh ∈ S.1 then (1 : F) else 0 at hTU
  rw [hTU]
  simp only [if_pos hz]
  have hcard : (S.1.erase (zeroIndex hh)).card = 2 := by
    rw [Finset.card_erase_of_mem hz, CenterCompression.triple_card S]
  -- direct sum over the complement label has the two remaining target entries
  have hones : dotProduct (indicator S.1) (allOnes (h := h)) = (S.1.card : F) := by
    simp [allOnes, dotProduct, indicator]
  rw [hones, CenterCompression.triple_card S]
  decide

lemma target_dot_dense_of_not_mem {h : ℕ} (hh : 1 ≤ h) (S : Triple h)
    (hz : zeroIndex hh ∉ S.1) :
    dotForm (indicator S.1)
      (denseComplementLabel (h := h) hh) = (1 : F) := by
  unfold denseComplementLabel
  change dotProduct (indicator S.1)
    (allOnes + unitLabel hh) = 1
  rw [dotProduct_add]
  have hTU := target_dot_unit hh S
  change dotProduct (indicator S.1) (unitLabel hh) =
      if zeroIndex hh ∈ S.1 then (1 : F) else 0 at hTU
  rw [hTU]
  simp only [if_neg hz]
  have hones : dotProduct (indicator S.1) (allOnes (h := h)) = (S.1.card : F) := by
    simp [allOnes, dotProduct, indicator]
  rw [hones, CenterCompression.triple_card S]
  decide

theorem exactly_one_targetBoundary_label {h : ℕ} (hh : 4 ≤ h)
    (heven : Even h) (S : Triple h) :
    (unitLabel (by omega : 1 ≤ h) ∈ targetBoundary S ∧
      denseComplementLabel (h := h) (by omega) ∉ targetBoundary S) ∨
    (unitLabel (by omega : 1 ≤ h) ∉ targetBoundary S ∧
      denseComplementLabel (h := h) (by omega) ∈ targetBoundary S) := by
  by_cases hz : zeroIndex (by omega : 1 ≤ h) ∈ S.1
  · right
    constructor
    · intro hu
      rw [targetBoundary, Submodule.orthogonalBilin_span_singleton] at hu
      change dotForm (indicator S.1) (unitLabel (by omega : 1 ≤ h)) = 0 at hu
      rw [target_dot_unit, if_pos hz] at hu
      exact one_ne_zero hu
    · rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
      change dotForm (indicator S.1)
        (denseComplementLabel (h := h) (by omega)) = 0
      rw [target_dot_dense_of_mem (by omega) S hz]
  · left
    constructor
    · rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
      change dotForm (indicator S.1) (unitLabel (by omega : 1 ≤ h)) = 0
      rw [target_dot_unit, if_neg hz]
    · intro hw
      rw [targetBoundary, Submodule.orthogonalBilin_span_singleton] at hw
      change dotForm (indicator S.1)
        (denseComplementLabel (h := h) (by omega)) = 0 at hw
      rw [target_dot_dense_of_not_mem (by omega) S hz] at hw
      exact one_ne_zero hw

/-- One nonzero active label cannot cover every target boundary.  This is the
rank/span obstruction, not a gate lower bound. -/
theorem no_single_nonzero_target_cover {h : ℕ} (hh : 4 ≤ h)
    {v : Active h} (hv : v ≠ 0) :
    ¬ (∀ S : Triple h, v ∈ targetBoundary S) := by
  intro hcover
  exact hv (all_target_boundaries_eq_zero_of_four hh hcover)

end ArbitraryTwoFrameCover
end ExactFourier
end OAI
