import OAI.Computability.FourierCircuit.TripleSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Incidence span of triples through one coordinate

For a fixed coordinate `i`, let `IncidenceSpan h i` be the span over `F₂` of
indicator vectors of three-element sets containing `i`.  This module records
the local frame facts used by the side-moment design: every such generator lies
in the hyperplane orthogonal to the complement label (zero at `i`, one
elsewhere), that hyperplane has dimension `h - 1`, and explicit incidence
combinations recover a coordinate vector and pair differences.  Equality of
the incidence span with the hyperplane, and any resulting circuit schedule,
are intentionally left open.

This is only a local label certificate.  It does not assert a complete framed
circuit or a complexity bound.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace IncidenceTripleSpan

open FrameLabels

abbrev K := ZMod 2
abbrev V (h : ℕ) := Fin h → K

/-- The complement of a fixed coordinate, written as a binary label. -/
def complementLabel {h : ℕ} (i : Fin h) : V h :=
  indicator (Finset.univ.erase i)

@[simp] theorem complementLabel_apply {h : ℕ} (i j : Fin h) :
    complementLabel i j = if j = i then 0 else 1 := by
  simp [complementLabel, indicator]

/-- Indicators of triples which contain the fixed coordinate. -/
def incidenceIndicators (h : ℕ) (i : Fin h) : Set (V h) :=
  {v | ∃ T : Finset (Fin h), T.card = 3 ∧ i ∈ T ∧ v = indicator T}

abbrev IncidenceSpan (h : ℕ) (i : Fin h) : Submodule K (V h) :=
  Submodule.span K (incidenceIndicators h i)

theorem incidence_indicator_mem {h : ℕ} {i : Fin h} (T : Finset (Fin h))
    (hT : T.card = 3) (hiT : i ∈ T) : indicator T ∈ IncidenceSpan h i := by
  exact Submodule.subset_span ⟨T, hT, hiT, rfl⟩

/-- Three incidence triples recover the `i`-th basis vector. -/
theorem basisVec_i_mem {h : ℕ} (hh : 4 ≤ h) (i a b c : Fin h)
    (hai : a ≠ i) (hbi : b ≠ i) (hba : b ≠ a)
    (hci : c ≠ i) (hca : c ≠ a) (hcb : c ≠ b) :
    TripleSpan.basisVec i ∈ IncidenceSpan h i := by
  have hab : ({i, a, b} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hbi, hbi.symm, hba, hba.symm]
  have hac : ({i, a, c} : Finset (Fin h)).card = 3 := by
    simp [hai, hai.symm, hci, hci.symm, hca, hca.symm]
  have hbc : ({i, b, c} : Finset (Fin h)).card = 3 := by
    simp [hbi, hbi.symm, hci, hci.symm, hcb, hcb.symm]
  have hiab := incidence_indicator_mem (i := i) ({i, a, b} : Finset (Fin h)) hab (by simp)
  have hiac := incidence_indicator_mem (i := i) ({i, a, c} : Finset (Fin h)) hac (by simp)
  have hibc := incidence_indicator_mem (i := i) ({i, b, c} : Finset (Fin h)) hbc (by simp)
  rw [TripleSpan.four_point_indicator_identity i a b c hai hbi hba hci hca hcb]
  exact (IncidenceSpan h i).add_mem ((IncidenceSpan h i).add_mem hiab hiac) hibc

/-- Two incidence triples recover a pair difference away from `i`. -/
theorem pair_difference_mem {h : ℕ} {i x b c : Fin h}
    (hix : x ≠ i) (hib : b ≠ i) (hcb : c ≠ b) (hcx : c ≠ x)
    (hxb : x ≠ b) (hci : c ≠ i) :
    TripleSpan.basisVec x + TripleSpan.basisVec b ∈ IncidenceSpan h i := by
  have hix' : i ≠ x := hix.symm
  have hib' : i ≠ b := hib.symm
  have hcx' : x ≠ c := hcx.symm
  have hcb' : b ≠ c := hcb.symm
  have hixb : ({i, x, c} : Finset (Fin h)).card = 3 := by
    simp [hix, hix', hci, hci.symm, hcx, hcx']
  have hibc : ({i, b, c} : Finset (Fin h)).card = 3 := by
    simp [hib, hib', hci, hci.symm, hcb, hcb']
  have h1 := incidence_indicator_mem (i := i) ({i, x, c} : Finset (Fin h)) hixb (by simp)
  have h2 := incidence_indicator_mem (i := i) ({i, b, c} : Finset (Fin h)) hibc (by simp)
  have hid : indicator ({i, x, c} : Finset (Fin h)) +
      indicator ({i, b, c} : Finset (Fin h)) =
      TripleSpan.basisVec x + TripleSpan.basisVec b := by
    funext j
    by_cases hji : j = i
    · subst j
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp [indicator, TripleSpan.basisVec, hix, hib, htwo] <;> decide
    · by_cases hjx : j = x
      · subst j
        have htwo : (2 : ZMod 2) = 0 := by decide
        simp [indicator, TripleSpan.basisVec, hix, hib, hxb, hxb.symm, hcx, hcx', htwo]
      · by_cases hjb : j = b
        · subst j
          have htwo : (2 : ZMod 2) = 0 := by decide
          simp [indicator, TripleSpan.basisVec, hix, hib, hxb, hxb.symm, hcb, hcb', htwo]
        · by_cases hjc : j = c
          · subst j
            have htwo : (2 : ZMod 2) = 0 := by decide
            simp [indicator, TripleSpan.basisVec, hix, hib, hxb, hxb.symm, hcx, hcx',
              hcb, hcb', htwo] <;> decide
          · simp [indicator, TripleSpan.basisVec, hji, hjx, hjb, hjc]
  rw [← hid]
  exact (IncidenceSpan h i).add_mem h1 h2

/-- Every incidence triple is orthogonal to the complement label (left orientation). -/
theorem incidence_indicator_orthogonal_left {h : ℕ} {i : Fin h}
    (T : Finset (Fin h)) (hT : T.card = 3) (hiT : i ∈ T) :
    dotForm (complementLabel i) (indicator T) = 0 := by
  have hinter : T ∩ (Finset.univ.erase i) = T.erase i := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
    tauto
  have hcard : (T ∩ (Finset.univ.erase i)).card = 2 := by
    rw [hinter, Finset.card_erase_of_mem hiT, hT]
  simpa [complementLabel] using
    (indicator_orthogonal_of_even T (Finset.univ.erase i) (by
      rw [hcard]
      exact even_two))

/-- The same orthogonality statement in the symmetric orientation. -/
theorem incidence_indicator_orthogonal {h : ℕ} {i : Fin h}
    (T : Finset (Fin h)) (hT : T.card = 3) (hiT : i ∈ T) :
    dotForm (indicator T) (complementLabel i) = 0 := by
  have hinter : (Finset.univ.erase i) ∩ T = T.erase i := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
    tauto
  have hcard : ((Finset.univ.erase i) ∩ T).card = 2 := by
    rw [hinter, Finset.card_erase_of_mem hiT, hT]
  simpa [complementLabel] using
    (indicator_orthogonal_of_even (Finset.univ.erase i) T (by
      rw [hcard]
      exact even_two))

/-- The incidence span is contained in the complement-label orthogonal hyperplane. -/
theorem incidenceSpan_le_orthogonal {h : ℕ} {i : Fin h} :
    IncidenceSpan h i ≤
      ((K ∙ complementLabel i).orthogonalBilin (dotForm : _)) := by
  apply Submodule.span_le.2
  rintro v ⟨T, hT, hiT, rfl⟩
  change ∀ z ∈ (K ∙ complementLabel i), dotForm z (indicator T) = 0
  intro z hz
  rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
  simp [map_smul, incidence_indicator_orthogonal_left T hT hiT]

/-- The complement-label functional is nonzero as soon as there is another coordinate. -/
theorem complement_functional_surjective {h : ℕ} (hh : 2 ≤ h) (i : Fin h) :
    Function.Surjective (dotForm (complementLabel i) : V h →ₗ[K] K) := by
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin h) (by
    rw [Fintype.card_fin]
    omega) i
  intro z
  refine ⟨z • TripleSpan.basisVec j, ?_⟩
  change dotForm (complementLabel i) (z • TripleSpan.basisVec j) = z
  rw [map_smul]
  have hsingle : TripleSpan.basisVec j = indicator ({j} : Finset (Fin h)) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [TripleSpan.basisVec, indicator]
    · simp [TripleSpan.basisVec, indicator, Pi.single, hkj]
  have hdot : dotForm (complementLabel i) (TripleSpan.basisVec j) = (1 : K) := by
    rw [hsingle]
    rw [show complementLabel i = indicator (Finset.univ.erase i) by rfl]
    rw [indicator_dot]
    simp [Pi.single_apply, hji]
  rw [hdot, smul_eq_mul, mul_one]

/-- The orthogonal complement has dimension `h - 1`. -/
theorem orthogonal_finrank {h : ℕ} (hh : 2 ≤ h) (i : Fin h) :
    Module.finrank K
      ((K ∙ complementLabel i).orthogonalBilin (dotForm : _)) = h - 1 := by
  rw [Submodule.orthogonalBilin_span_singleton]
  let f : V h →ₗ[K] K := dotForm (complementLabel i)
  have hsurj : Function.Surjective f := complement_functional_surjective hh i
  have hrange : LinearMap.range f = (⊤ : Submodule K K) :=
    LinearMap.range_eq_top.2 hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  change Module.finrank K (LinearMap.ker f) = h - 1
  rw [hrange, finrank_top] at hrank
  have hdim : Module.finrank K (V h) = h := by
    exact Module.finrank_fin_fun K
  rw [hdim] at hrank
  have hrank' : 1 + Module.finrank K (LinearMap.ker f) = h := by
    simpa using hrank
  omega

end IncidenceTripleSpan
end ExactFourier
end OAI
