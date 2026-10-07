import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import Mathlib.Tactic

/-!
# Pair-span round-trip dimensions

For a fixed pair F, the all-target pair labels have span of dimension h - 2.
If an auxiliary role starts and ends in the full active frame and is routed
through that pair span, the two nested edges each have residual dimension two.
Their dimensional charge is therefore exactly four.

This is a local frame accounting lemma. It does not claim that every
side-wire construction must use this route; it records the precise premise
behind the four-unit pair-prefix obstruction.
-/

namespace OAI
namespace ExactFourier
namespace PairSpanRoundtripCost

open PairTargetFrameLocal
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- The full-to-pair residual dimension, for a pair span known to be nested
in the full active space. -/
noncomputable def fullToPairCost {h : ℕ}
    (P : Submodule F (Active h)) : ℕ :=
  Module.finrank F (Active h) - Module.finrank F P

/-- A pair span has codimension two in the active factor. -/
theorem pairSpan_codim_two {h : ℕ}
    (F₀ : Finset (Fin h)) (hF : F₀.card = 2) (hh : 4 ≤ h) :
    fullToPairCost (pairSpan F₀) = 2 := by
  unfold fullToPairCost
  rw [pairSpan_finrank F₀ hF]
  simp [Active]
  omega

/-- Leaving and returning to one pair span costs exactly four residual
  directions when both endpoint labels are the full active frame. -/
theorem pairSpan_roundtrip_cost_eq_four {h : ℕ}
    (F₀ : Finset (Fin h)) (hF : F₀.card = 2) (hh : 4 ≤ h) :
    fullToPairCost (pairSpan F₀) + fullToPairCost (pairSpan F₀) = 4 := by
  rw [pairSpan_codim_two F₀ hF hh]

/-- A pair span cannot be kept inside every target-coordinate hyperplane.
This is the local nesting obstruction behind the need for frame changes when
one global pair aggregate is touched by all target choices. -/
theorem pairSpan_not_le_all_target_hyperplanes {h : ℕ}
    (F₀ : Finset (Fin h)) (hF : F₀.card = 2) (hh : 4 ≤ h) :
    ¬ ∃ J : Submodule F (Active h), pairSpan F₀ ≤ J ∧
      ∀ k : Fin h, k ∉ F₀ → J ≤ coordinateHyperplane k := by
  rintro ⟨J, hpair, hall⟩
  have hFlt : F₀.card < (Finset.univ : Finset (Fin h)).card := by
    rw [hF, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hk_univ, hkF⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hFlt
  let p : PairIndex F₀ := ⟨k, hkF⟩
  have hp : pairLabel F₀ p ∈ pairSpan F₀ :=
    Submodule.subset_span (Set.mem_range_self p)
  have hk : pairLabel F₀ p ∈ coordinateHyperplane k :=
    (hall k hkF) (hpair hp)
  change pairLabel F₀ p k = 0 at hk
  rw [show k = p.val by rfl, pairLabel_pair_coordinate F₀ p p] at hk
  simp at hk

end PairSpanRoundtripCost
end ExactFourier
end OAI
