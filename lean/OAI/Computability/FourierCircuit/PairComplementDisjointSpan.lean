import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Rank certificate for the disjoint-triple pair bank

For a fixed pair `F`, the `B_F` aggregate sees indicators of triples disjoint
from `F`.  This file proves that those indicators span exactly the coordinate
submodule which vanishes on `F`; hence its rank is `h - |F|`.  The proof is a
local binary-label fact only.  It supplies the rank premise used by the
aggregate-wise boundary ledger, but does not build the corresponding gate
transport.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace PairComplementDisjointSpan

open FrameLabels
open TripleSpan

abbrev K := ZMod 2
abbrev V (h : ℕ) := Fin h → K

def disjointTripleIndicators {h : ℕ} (F : Finset (Fin h)) : Set (V h) :=
  {v | ∃ T : Finset (Fin h), T.card = 3 ∧ Disjoint F T ∧ v = indicator T}

abbrev disjointTripleSpan {h : ℕ} (F : Finset (Fin h)) :
    Submodule K (V h) := Submodule.span K (disjointTripleIndicators F)

theorem disjoint_indicator_mem {h : ℕ} (F T : Finset (Fin h))
    (hT : T.card = 3) (hFT : Disjoint F T) :
    indicator T ∈ disjointTripleSpan F := by
  exact Submodule.subset_span ⟨T, hT, hFT, rfl⟩

/- The coordinate submodule complementary to the fixed pair. -/
def awaySubmodule {h : ℕ} (F : Finset (Fin h)) : Submodule K (V h) where
  carrier := {x | ∀ i, i ∈ F → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro a x hx i hi
    simp [hx i hi]

theorem disjointTripleSpan_le_awaySubmodule {h : ℕ} (F : Finset (Fin h)) :
    disjointTripleSpan F ≤ awaySubmodule F := by
  apply Submodule.span_le.2
  rintro v ⟨T, hT, hFT, rfl⟩
  intro i hiF
  have hzero : i ∉ T := by
    intro hiT
    exact (Finset.disjoint_left.1 hFT hiF hiT)
  simp [indicator, hzero]

theorem basisVec_mem_disjointTripleSpan {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 6 ≤ h) (i : Fin h) (hiF : i ∉ F) :
    TripleSpan.basisVec i ∈ disjointTripleSpan F := by
  classical
  let forbidden : Finset (Fin h) := insert i F
  have hforbidden : forbidden.card = 3 := by
    simp [forbidden, hiF, hF]
  have hlt : forbidden.card < (Finset.univ : Finset (Fin h)).card := by
    rw [hforbidden, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, hauniv, haforbidden⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  let forbiddenA : Finset (Fin h) := insert a forbidden
  have hforbiddenA : forbiddenA.card = 4 := by
    have hai : a ∉ forbidden := haforbidden
    simp [forbiddenA, hforbidden, hai]
  have hltA : forbiddenA.card < (Finset.univ : Finset (Fin h)).card := by
    rw [hforbiddenA, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, hbuniv, hbforbiddenA⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hltA
  let forbiddenB : Finset (Fin h) := insert b forbiddenA
  have hforbiddenB : forbiddenB.card = 5 := by
    have hba : b ∉ forbiddenA := hbforbiddenA
    simp [forbiddenB, hforbiddenA, hba]
  have hltB : forbiddenB.card < (Finset.univ : Finset (Fin h)).card := by
    rw [hforbiddenB, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hcuniv, hcforbiddenB⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hltB
  have hai : a ≠ i := by
    intro hEq
    exact haforbidden (by simp [forbidden, hEq])
  have hbi : b ≠ i := by
    intro hEq
    exact hbforbiddenA (by simp [forbiddenA, forbidden, hEq])
  have hba : b ≠ a := by
    intro hEq
    exact hbforbiddenA (by simp [forbiddenA, hEq])
  have hci : c ≠ i := by
    intro hEq
    exact hcforbiddenB (by simp [forbiddenB, forbiddenA, forbidden, hEq])
  have hca : c ≠ a := by
    intro hEq
    exact hcforbiddenB (by simp [forbiddenB, forbiddenA, hEq])
  have hcb : c ≠ b := by
    intro hEq
    exact hcforbiddenB (by simp [forbiddenB, hEq])
  have haF : a ∉ F := by
    intro ha
    exact haforbidden (by simp [forbidden, ha])
  have hbF : b ∉ F := by
    intro hb
    exact hbforbiddenA (by simp [forbiddenA, forbidden, hb])
  have hcF : c ∉ F := by
    intro hc
    exact hcforbiddenB (by simp [forbiddenB, forbiddenA, forbidden, hc])
  have hab : ({i, a, b} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hbi, hbi.symm, hba, hba.symm]
  have hac : ({i, a, c} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hci, hci.symm, hca, hca.symm]
  have hbc : ({i, b, c} : Finset (Fin h)).card = 3 := by
    simp [hbi, hbi.symm, hci, hci.symm, hcb, hcb.symm]
  have hdisab : Disjoint F ({i, a, b} : Finset (Fin h)) := by
    rw [Finset.disjoint_left]
    intro j hjF hjT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjT
    rcases hjT with rfl | rfl | rfl
    · exact hiF hjF
    · exact haF hjF
    · exact hbF hjF
  have hdisac : Disjoint F ({i, a, c} : Finset (Fin h)) := by
    rw [Finset.disjoint_left]
    intro j hjF hjT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjT
    rcases hjT with rfl | rfl | rfl
    · exact hiF hjF
    · exact haF hjF
    · exact hcF hjF
  have hdisbc : Disjoint F ({i, b, c} : Finset (Fin h)) := by
    rw [Finset.disjoint_left]
    intro j hjF hjT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjT
    rcases hjT with rfl | rfl | rfl
    · exact hiF hjF
    · exact hbF hjF
    · exact hcF hjF
  have hiab := disjoint_indicator_mem F ({i, a, b} : Finset (Fin h)) hab hdisab
  have hiac := disjoint_indicator_mem F ({i, a, c} : Finset (Fin h)) hac hdisac
  have hibc := disjoint_indicator_mem F ({i, b, c} : Finset (Fin h)) hbc hdisbc
  rw [TripleSpan.four_point_indicator_identity i a b c hai hbi hba hci hca hcb]
  exact (disjointTripleSpan F).add_mem ((disjointTripleSpan F).add_mem hiab hiac) hibc

theorem awaySubmodule_le_disjointTripleSpan {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 6 ≤ h) :
    awaySubmodule F ≤ disjointTripleSpan F := by
  intro x hx
  have hsum : x = ∑ i : Fin h, x i • TripleSpan.basisVec i := by
    funext j
    simp [Finset.sum_apply, TripleSpan.basisVec, Pi.single_apply,
      smul_eq_mul, mul_ite]
  rw [hsum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hiF : i ∈ F
  · have hz := hx i hiF
    simp [hz]
  · exact Submodule.smul_mem _ _ (basisVec_mem_disjointTripleSpan F hF hh i hiF)

theorem disjointTripleSpan_eq_awaySubmodule {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 6 ≤ h) :
    disjointTripleSpan F = awaySubmodule F := by
  exact le_antisymm (disjointTripleSpan_le_awaySubmodule F)
    (awaySubmodule_le_disjointTripleSpan F hF hh)

def coordinateRestriction {h : ℕ} (F : Finset (Fin h)) :
    V h →ₗ[K] ((↥F) → K) where
  toFun x i := x i.1
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordinateRestriction_surjective {h : ℕ} (F : Finset (Fin h)) :
    Function.Surjective (coordinateRestriction F) := by
  intro y
  let x : V h := fun i => if hi : i ∈ F then y ⟨i, hi⟩ else 0
  refine ⟨x, ?_⟩
  funext i
  simp [coordinateRestriction, x]

theorem coordinateRestriction_ker {h : ℕ} (F : Finset (Fin h)) :
    LinearMap.ker (coordinateRestriction F) = awaySubmodule F := by
  ext x
  constructor
  · intro hx i hi
    have hxi := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
    exact hxi
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext i
    exact hx i.1 i.2

theorem awaySubmodule_finrank {h : ℕ} (F : Finset (Fin h)) :
    Module.finrank K (awaySubmodule F) = h - F.card := by
  let f := coordinateRestriction F
  have hf : Function.Surjective f := by
    exact coordinateRestriction_surjective F
  have hrange : LinearMap.range f = (⊤ : Submodule K ((↥F) → K)) :=
    LinearMap.range_eq_top.mpr hf
  have hsum := f.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, coordinateRestriction_ker] at hsum
  have hdimV : Module.finrank K (V h) = h := by
    simp [V, Module.finrank_pi]
  have hdimF : Module.finrank K ((↥F) → K) = F.card := by
    simpa using (Module.finrank_pi K : Module.finrank K ((↥F) → K) = Fintype.card F)
  rw [hdimV, hdimF] at hsum
  omega

theorem disjointTripleSpan_finrank {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 6 ≤ h) :
    Module.finrank K (disjointTripleSpan F) = h - 2 := by
  rw [disjointTripleSpan_eq_awaySubmodule F hF hh]
  simpa [hF] using awaySubmodule_finrank F

namespace H24

theorem pair_disjointTripleSpan_rank (F : Finset (Fin 24))
    (hF : F.card = 2) :
    Module.finrank K (disjointTripleSpan F) = 22 := by
  simpa using disjointTripleSpan_finrank F hF (by norm_num)

end H24
end PairComplementDisjointSpan
end ExactFourier
end OAI
