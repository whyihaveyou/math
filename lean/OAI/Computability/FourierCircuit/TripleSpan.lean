import OAI.Computability.FourierCircuit.FrameLabels
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Span of triple indicators

For `h ≥ 4`, the indicator vectors of all three-element subsets of `Fin h`
span `(Fin h → ZMod 2)`.  The proof uses the four-point identity

`e_i = 1_{i,a,b} + 1_{i,a,c} + 1_{i,b,c}`

for four pairwise distinct points.  This is only a linear-algebra certificate;
it does not formalize the complete frame-labelled network or any circuit bound.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace TripleSpan

open FrameLabels

def tripleIndicators (h : ℕ) : Set (Fin h → ZMod 2) :=
  {v | ∃ T : Finset (Fin h), T.card = 3 ∧ v = indicator T}

abbrev TripleSpan (h : ℕ) : Submodule (ZMod 2) (Fin h → ZMod 2) :=
  Submodule.span (ZMod 2) (tripleIndicators h)

def basisVec {h : ℕ} (i : Fin h) : Fin h → ZMod 2 := Pi.single i 1

theorem indicator_mem_span {h : ℕ} (T : Finset (Fin h)) (hT : T.card = 3) :
    indicator T ∈ TripleSpan h := by
  apply Submodule.subset_span
  exact ⟨T, hT, rfl⟩

theorem exists_three_away {h : ℕ} (hh : 3 < h) (i : Fin h) :
    ∃ a b c : Fin h,
      a ≠ i ∧ b ≠ i ∧ b ≠ a ∧ c ≠ i ∧ c ≠ a ∧ c ≠ b := by
  obtain ⟨a, hai⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := Fin h) (by
      rw [Fintype.card_fin]
      omega) i
  obtain ⟨b, hbi, hba⟩ := Fin.exists_ne_and_ne_of_two_lt i a (by omega)
  let forbidden : Finset (Fin h) := {i, a, b}
  have hforbidden : forbidden.card = 3 := by
    simp [forbidden, hai, hai.symm, hbi, hbi.symm, hba, hba.symm]
  have hlt : forbidden.card < (Finset.univ : Finset (Fin h)).card := by
    rw [hforbidden, Finset.card_univ]
    rw [Fintype.card_fin]
    exact hh
  obtain ⟨c, hcuniv, hcforbidden⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, b, c, hai, hbi, hba, ?_, ?_, ?_⟩
  · intro hci
    apply hcforbidden
    simp [forbidden, hci]
  · intro hca
    apply hcforbidden
    simp [forbidden, hca]
  · intro hcb
    apply hcforbidden
    simp [forbidden, hcb]

theorem four_point_indicator_identity {h : ℕ} (i a b c : Fin h)
    (hai : a ≠ i) (hbi : b ≠ i) (hba : b ≠ a)
    (hci : c ≠ i) (hca : c ≠ a) (hcb : c ≠ b) :
    basisVec i = indicator {i, a, b} + indicator {i, a, c} + indicator {i, b, c} := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [basisVec, indicator, hai, hbi, hba, hci, hca, hcb] <;> decide
  · by_cases hja : j = a
    · subst j
      simp [basisVec, indicator, hai, hbi, hba, hba.symm, hci, hca, hcb, hca.symm] <;>
        decide
    · by_cases hjb : j = b
      · subst j
        simp [basisVec, indicator, hai, hbi, hba, hba.symm, hci, hca, hcb,
          hcb.symm] <;> decide
      · by_cases hjc : j = c
        · subst j
          simp [basisVec, indicator, hai, hbi, hba, hba.symm, hci, hca, hcb,
            hcb.symm, hca.symm] <;> decide
        · simp [basisVec, indicator, hji, hja, hjb, hjc] <;> decide

theorem basisVec_mem_span {h : ℕ} (hh : 3 < h) (i : Fin h) :
    basisVec i ∈ TripleSpan h := by
  obtain ⟨a, b, c, hai, hbi, hba, hci, hca, hcb⟩ := exists_three_away hh i
  have hab : ({i, a, b} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hbi, hbi.symm, hba, hba.symm]
  have hac : ({i, a, c} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hci, hci.symm, hca, hca.symm]
  have hbc : ({i, b, c} : Finset (Fin h)).card = 3 := by
    simp [hbi, hbi.symm, hci, hci.symm, hcb, hcb.symm]
  have hiab := indicator_mem_span ({i, a, b} : Finset (Fin h)) hab
  have hiac := indicator_mem_span ({i, a, c} : Finset (Fin h)) hac
  have hibc := indicator_mem_span ({i, b, c} : Finset (Fin h)) hbc
  rw [four_point_indicator_identity i a b c hai hbi hba hci hca hcb]
  exact (TripleSpan h).add_mem ((TripleSpan h).add_mem hiab hiac) hibc

theorem tripleIndicators_span_eq_top {h : ℕ} (hh : 3 < h) :
    TripleSpan h = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun (ZMod 2) (Fin h))).2
  intro i
  rw [Pi.basisFun_apply]
  exact basisVec_mem_span hh i

theorem tripleIndicators_span_eq_top_of_four {h : ℕ} (hh : 4 ≤ h) :
    TripleSpan h = ⊤ := by
  exact tripleIndicators_span_eq_top (by omega)

theorem contains_all_triple_indicators_eq_top {h : ℕ} (hh : 3 < h)
    (S : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hS : ∀ T : Finset (Fin h), T.card = 3 → indicator T ∈ S) :
    S = ⊤ := by
  apply le_antisymm le_top
  rw [← tripleIndicators_span_eq_top hh]
  apply Submodule.span_le.2
  intro x hx
  rcases hx with ⟨T, hT, rfl⟩
  exact hS T hT

theorem h24_tripleIndicators_span_eq_top :
    TripleSpan 24 = ⊤ := by
  exact tripleIndicators_span_eq_top_of_four (by norm_num)

end TripleSpan
end ExactFourier
end OAI
