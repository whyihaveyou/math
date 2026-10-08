import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-!
# A joint-gate barrier for pair/complement side banks

For a fixed target triple, the three pair banks whose pairs lie inside the
triple cannot share a single low-dimensional active frame: their generated
binary label join is already the full active factor.  This is a local label
fact, not a lower bound for arbitrary complex circuits.  It rules out only the
naive implementation that touches all target pair aggregates through one
common rank-`h-2` frame.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementJointGateJoin

open FrameLabels
open PairTargetFrameLocal

abbrev K := ZMod 2
abbrev V (h : ℕ) := Fin h → K

/-- The three pair-bank frames for the explicit target `{0,1,2}`. -/
def targetPairJoinH24 : Submodule K (V 24) :=
  pairSpan ({0, 1} : Finset (Fin 24)) ⊔
    pairSpan ({0, 2} : Finset (Fin 24)) ⊔
      pairSpan ({1, 2} : Finset (Fin 24))

private lemma indicator_reorder {h : ℕ} (a b c : Fin h) :
    indicator ({a, b, c} : Finset (Fin h)) =
      indicator (insert c ({a, b} : Finset (Fin h))) := by
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

private lemma pair_label_mem_pairSpan {h : ℕ}
    (F : Finset (Fin h)) (j : Fin h) (hj : j ∉ F) :
    indicator (insert j F) ∈ pairSpan F := by
  let pj : PairIndex F := ⟨j, hj⟩
  exact Submodule.subset_span (Set.mem_range_self pj)

private lemma pair01_mem (j : Fin 24) (hj : j ∉ ({0, 1} : Finset (Fin 24))) :
    indicator (insert j ({0, 1} : Finset (Fin 24))) ∈ targetPairJoinH24 := by
  have hle : pairSpan ({0, 1} : Finset (Fin 24)) ≤ targetPairJoinH24 :=
    le_sup_of_le_left (le_sup_of_le_left le_rfl)
  exact hle (pair_label_mem_pairSpan _ _ hj)

private lemma pair02_mem (j : Fin 24) (hj : j ∉ ({0, 2} : Finset (Fin 24))) :
    indicator (insert j ({0, 2} : Finset (Fin 24))) ∈ targetPairJoinH24 := by
  have hle : pairSpan ({0, 2} : Finset (Fin 24)) ≤ targetPairJoinH24 :=
    le_sup_of_le_left (le_sup_of_le_right le_rfl)
  exact hle (pair_label_mem_pairSpan _ _ hj)

private lemma pair12_mem (j : Fin 24) (hj : j ∉ ({1, 2} : Finset (Fin 24))) :
    indicator (insert j ({1, 2} : Finset (Fin 24))) ∈ targetPairJoinH24 := by
  have hle : pairSpan ({1, 2} : Finset (Fin 24)) ≤ targetPairJoinH24 :=
    le_sup_of_le_right le_rfl
  exact hle (pair_label_mem_pairSpan _ _ hj)

private lemma targetPairJoinH24_contains
    {T : Finset (Fin 24)} (hT : T.card = 3)
    (hmem : indicator T ∈ targetPairJoinH24) :
    indicator T ∈ targetPairJoinH24 := hmem

/-- The explicit target `{0,1,2}` has a full pair-bank join in dimension 24. -/
theorem h24_target_pair_join_eq_top : targetPairJoinH24 = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K (Fin 24))).2
  intro i
  rw [Pi.basisFun_apply]
  change TripleSpan.basisVec i ∈ targetPairJoinH24
  by_cases hi0 : i = 0
  · subst i
    have h4 := TripleSpan.four_point_indicator_identity (0 : Fin 24) 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [h4]
    have h012 : indicator ({0, 1, 2} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
      rw [indicator_reorder]
      exact pair01_mem 2 (by decide)
    have h013 : indicator ({0, 1, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
      rw [indicator_reorder]
      exact pair01_mem 3 (by decide)
    have h023 : indicator ({0, 2, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
      rw [indicator_reorder]
      exact pair02_mem 3 (by decide)
    exact targetPairJoinH24.add_mem (targetPairJoinH24.add_mem h012 h013) h023
  · by_cases hi1 : i = 1
    · subst i
      have h4 := TripleSpan.four_point_indicator_identity (1 : Fin 24) 0 2 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [h4]
      have h102 : indicator ({1, 0, 2} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
        convert pair01_mem 2 (by decide) using 1 <;>
          congr 1 <;> ext x <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] <;> aesop
      have h103 : indicator ({1, 0, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
        convert pair01_mem 3 (by decide) using 1 <;>
          congr 1 <;> ext x <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] <;> aesop
      have h123 : indicator ({1, 2, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
        rw [indicator_reorder]
        exact pair12_mem 3 (by decide)
      exact targetPairJoinH24.add_mem (targetPairJoinH24.add_mem h102 h103) h123
    · by_cases hi2 : i = 2
      · subst i
        have h4 := TripleSpan.four_point_indicator_identity (2 : Fin 24) 0 1 3
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        rw [h4]
        have h201 : indicator ({2, 0, 1} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          convert pair02_mem 1 (by decide) using 1 <;>
            congr 1 <;> ext x <;>
            simp only [Finset.mem_insert, Finset.mem_singleton] <;> aesop
        have h203 : indicator ({2, 0, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          convert pair02_mem 3 (by decide) using 1 <;>
            congr 1 <;> ext x <;>
            simp only [Finset.mem_insert, Finset.mem_singleton] <;> aesop
        have h213 : indicator ({2, 1, 3} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          convert pair12_mem 3 (by decide) using 1 <;>
            congr 1 <;> ext x <;>
            simp only [Finset.mem_insert, Finset.mem_singleton] <;> aesop
        exact targetPairJoinH24.add_mem (targetPairJoinH24.add_mem h201 h203) h213
      · have h4 := TripleSpan.four_point_indicator_identity i 0 1 2
          (by intro h; exact hi0 h.symm)
          (by intro h; exact hi1 h.symm)
          (by decide)
          (by intro h; exact hi2 h.symm)
          (by decide) (by decide)
        rw [h4]
        have hiF01 : i ∉ ({0, 1} : Finset (Fin 24)) := by simp [hi0, hi1]
        have hiF02 : i ∉ ({0, 2} : Finset (Fin 24)) := by simp [hi0, hi2]
        have hiF12 : i ∉ ({1, 2} : Finset (Fin 24)) := by simp [hi1, hi2]
        have hi012 : indicator ({i, 0, 1} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          exact pair01_mem i hiF01
        have hi020 : indicator ({i, 0, 2} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          exact pair02_mem i hiF02
        have hi121 : indicator ({i, 1, 2} : Finset (Fin 24)) ∈ targetPairJoinH24 := by
          exact pair12_mem i hiF12
        exact targetPairJoinH24.add_mem (targetPairJoinH24.add_mem hi012 hi020) hi121

end PairComplementJointGateJoin
end ExactFourier
end OAI
