import OAI.Computability.FourierCircuit.BinaryTransvection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
# Local source span for a diagonal-excluded pair prefix

Fix a pair `F` and a target triple `insert k F`, where `k ∉ F`.
The off-diagonal source triples containing `F` are precisely `insert j F`
with `j ∉ insert k F`.  Their indicator vectors vanish at coordinate `k`.
They are linearly independent: their coordinates outside `insert k F`
recover the coefficients individually.  Consequently their span has dimension
`h - 3`.

This module is a local label certificate.  It supplies neither a shared frame
across different targets nor an implementation or cost bound for a circuit.
-/

open scoped BigOperators

namespace OAI.ExactFourier.PairTargetFrameLocal

open FrameLabels

abbrev K := ZMod 2
abbrev V (h : ℕ) := Fin h → K

/-- The third source coordinates after excluding the target triple. -/
def sourceCoordinates {h : ℕ} (F : Finset (Fin h)) (k : Fin h) : Finset (Fin h) :=
  Finset.univ \ insert k F

abbrev SourceIndex {h : ℕ} (F : Finset (Fin h)) (k : Fin h) :=
  {j : Fin h // j ∈ sourceCoordinates F k}

@[simp] theorem mem_sourceCoordinates {h : ℕ} (F : Finset (Fin h)) (k j : Fin h) :
    j ∈ sourceCoordinates F k ↔ j ≠ k ∧ j ∉ F := by
  simp [sourceCoordinates]

/-- The indicator of an off-diagonal source triple through the fixed pair. -/
def sourceLabel {h : ℕ} (F : Finset (Fin h)) (k : Fin h)
    (j : SourceIndex F k) : V h := indicator (insert j.val F)

/-- The target-dependent source span, with its full generating family explicit. -/
def sourceSpan {h : ℕ} (F : Finset (Fin h)) (k : Fin h) : Submodule K (V h) :=
  Submodule.span K (Set.range (sourceLabel F k))

theorem sourceLabel_mem {h : ℕ} (F : Finset (Fin h)) (k : Fin h)
    (j : SourceIndex F k) : sourceLabel F k j ∈ sourceSpan F k :=
  Submodule.subset_span (Set.mem_range_self j)

/-- Each generator has target coordinate zero. -/
@[simp] theorem sourceLabel_target_coordinate {h : ℕ} (F : Finset (Fin h))
    (k : Fin h) (hk : k ∉ F) (j : SourceIndex F k) :
    sourceLabel F k j k = 0 := by
  have hj := (mem_sourceCoordinates F k j.val).mp j.property
  simp [sourceLabel, indicator, hk, Ne.symm hj.1]

/-- The full span lies in the target-coordinate hyperplane. -/
theorem sourceSpan_le_coordinateHyperplane {h : ℕ} (F : Finset (Fin h))
    (k : Fin h) (hk : k ∉ F) :
    sourceSpan F k ≤ BinaryTransvection.coordinateHyperplane k := by
  apply Submodule.span_le.mpr
  rintro v ⟨j, rfl⟩
  exact sourceLabel_target_coordinate F k hk j

/-- Restricting the source-label matrix to the source coordinates gives an identity matrix. -/
@[simp] theorem sourceLabel_source_coordinate {h : ℕ} (F : Finset (Fin h))
    (k : Fin h) (i j : SourceIndex F k) :
    sourceLabel F k i j.val = if i = j then 1 else 0 := by
  have hj := (mem_sourceCoordinates F k j.val).mp j.property
  by_cases hij : i = j
  · subst i
    simp [sourceLabel, indicator]
  · have hval : j.val ≠ i.val := fun heq => hij (Subtype.ext heq.symm)
    simp [sourceLabel, indicator, hj.2, hval, hij]

/-- Source-coordinate evaluation reads each coefficient in an arbitrary linear combination. -/
theorem combination_source_coordinate {h : ℕ} (F : Finset (Fin h))
    (k : Fin h) (c : SourceIndex F k → K) (j : SourceIndex F k) :
    (∑ i, c i • sourceLabel F k i) j.val = c j := by
  simp [Finset.sum_apply, sourceLabel_source_coordinate]

/-- No nontrivial combination of distinct off-diagonal source triples vanishes. -/
theorem sourceLabel_linearIndependent {h : ℕ} (F : Finset (Fin h)) (k : Fin h) :
    LinearIndependent K (sourceLabel F k) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hj := congrFun hc j.val
  simpa only [combination_source_coordinate, Pi.zero_apply] using hj

/-- Vanishing on every source coordinate forces a vector in the source span to vanish. -/
theorem sourceSpan_eq_zero_of_source_coordinates_zero {h : ℕ}
    (F : Finset (Fin h)) (k : Fin h) (x : V h)
    (hx : x ∈ sourceSpan F k)
    (hxzero : ∀ j : Fin h, j ∈ sourceCoordinates F k → x j = 0) :
    x = 0 := by
  rw [sourceSpan] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  have hczero : ∀ j : SourceIndex F k, c j = 0 := by
    intro j
    have hcoord := congrFun hc j.val
    rw [combination_source_coordinate] at hcoord
    rw [hxzero j.val j.property] at hcoord
    exact hcoord
  simpa [hczero] using hc.symm

/-- All target-dependent diagonal-excluded pair spans have zero common intersection. -/
theorem common_sourceSpan_eq_bot {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) (x : V h)
    (hx : ∀ k : Fin h, k ∉ F → x ∈ sourceSpan F k) :
    x = 0 := by
  have hFlt : F.card < (Finset.univ : Finset (Fin h)).card := by
    simpa [hF, Finset.card_univ] using (show 2 < h by omega)
  obtain ⟨k, hk_univ, hkF⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hFlt
  have hxout : ∀ j : Fin h, j ∉ F → x j = 0 := by
    intro j hj
    have hjmem : x ∈ BinaryTransvection.coordinateHyperplane j := by
      exact sourceSpan_le_coordinateHyperplane F j hj (hx j hj)
    change x j = 0 at hjmem
    exact hjmem
  apply sourceSpan_eq_zero_of_source_coordinates_zero F k x (hx k hkF)
  intro j hj
  exact hxout j ((mem_sourceCoordinates F k j).mp hj).2

theorem sourceIndex_card {h : ℕ} (F : Finset (Fin h)) (k : Fin h)
    (hF : F.card = 2) (hk : k ∉ F) :
    Fintype.card (SourceIndex F k) = h - 3 := by
  change Fintype.card {j // j ∈ sourceCoordinates F k} = h - 3
  rw [Fintype.card_coe]
  simp [sourceCoordinates, Finset.card_sdiff,
    Finset.card_insert_of_notMem hk, hF]

/-- The local source span has the exact dimension `h - 3`. -/
theorem sourceSpan_finrank {h : ℕ} (F : Finset (Fin h)) (k : Fin h)
    (hF : F.card = 2) (hk : k ∉ F) :
    Module.finrank K (sourceSpan F k) = h - 3 := by
  rw [sourceSpan, finrank_span_eq_card (sourceLabel_linearIndependent F k)]
  exact sourceIndex_card F k hF hk


/-- All possible third coordinates of a pair, before excluding a target. -/
abbrev PairIndex {h : ℕ} (F : Finset (Fin h)) :=
  {j : Fin h // j ∉ F}

def pairLabel {h : ℕ} (F : Finset (Fin h))
    (j : PairIndex F) : V h := indicator (insert j.val F)

def pairSpan {h : ℕ} (F : Finset (Fin h)) : Submodule K (V h) :=
  Submodule.span K (Set.range (pairLabel F))

@[simp] theorem pairLabel_pair_coordinate {h : ℕ} (F : Finset (Fin h))
    (i j : PairIndex F) :
    pairLabel F i j.val = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    simp [pairLabel, indicator]
  · have hval : j.val ≠ i.val := fun heq => hij (Subtype.ext heq.symm)
    simp [pairLabel, indicator, i.property, j.property, hval, hij]

theorem pairLabel_linearIndependent {h : ℕ} (F : Finset (Fin h)) :
    LinearIndependent K (pairLabel F) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hcoord := congrFun hc j.val
  simpa [Finset.sum_apply, pairLabel_pair_coordinate] using hcoord

theorem pairIndex_card {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) :
    Fintype.card (PairIndex F) = h - 2 := by
  have hcard : Fintype.card {j : Fin h // j ∈ F} = F.card := by
    exact Fintype.card_coe F
  rw [Fintype.card_subtype_compl (fun j : Fin h => j ∈ F),
    Fintype.card_fin, hcard, hF]

theorem pairSpan_finrank {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) :
    Module.finrank K (pairSpan F) = h - 2 := by
  rw [pairSpan, finrank_span_eq_card (pairLabel_linearIndependent F)]
  exact pairIndex_card F hF

theorem sourceSpan_le_pairSpan {h : ℕ} (F : Finset (Fin h)) (k : Fin h) :
    sourceSpan F k ≤ pairSpan F := by
  apply Submodule.span_le.mpr
  rintro v ⟨j, rfl⟩
  apply Submodule.subset_span
  have hj : j.val ∉ F := (mem_sourceCoordinates F k j.val).mp j.property |>.2
  let j' : PairIndex F := ⟨j.val, hj⟩
  exact Set.mem_range_self j'

def allTargetSourceSpan {h : ℕ} (F : Finset (Fin h)) : Submodule K (V h) :=
  ⨆ k : PairIndex F, sourceSpan F k.val

theorem allTargetSourceSpan_le_pairSpan {h : ℕ} (F : Finset (Fin h)) :
    allTargetSourceSpan F ≤ pairSpan F := by
  apply iSup_le
  intro k
  exact sourceSpan_le_pairSpan F k.val

/-- For `h ≥ 4`, every pair source label appears in some target-excluded span. -/
theorem pairSpan_le_allTargetSourceSpan {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) :
    pairSpan F ≤ allTargetSourceSpan F := by
  apply Submodule.span_le.mpr
  rintro v ⟨j, rfl⟩
  have hout : (Finset.univ \ F : Finset (Fin h)).card = h - 2 := by
    simp [Finset.card_sdiff, hF]
  have hlt : ({j.val} : Finset (Fin h)).card <
      (Finset.univ \ F : Finset (Fin h)).card := by
    rw [hout]
    have : 2 ≤ h - 2 := by omega
    simp only [Finset.card_singleton]
    omega
  obtain ⟨k, hkout, hkj⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  have hkF : k ∉ F := (Finset.mem_sdiff.mp hkout).2
  have hkj' : j.val ≠ k := by
    intro hEq
    apply hkj
    simp [hEq]
  let t : SourceIndex F k :=
    ⟨j.val, (mem_sourceCoordinates F k j.val).2 ⟨hkj', j.property⟩⟩
  have ht : sourceLabel F k t ∈ sourceSpan F k := sourceLabel_mem F k t
  have ht' : sourceLabel F k t ∈ allTargetSourceSpan F :=
    Submodule.mem_iSup_of_mem ⟨k, hkF⟩ ht
  exact ht'

theorem allTargetSourceSpan_eq_pairSpan {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) :
    allTargetSourceSpan F = pairSpan F := by
  exact le_antisymm (allTargetSourceSpan_le_pairSpan F)
    (pairSpan_le_allTargetSourceSpan F hF hh)

theorem allTargetSourceSpan_finrank {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) :
    Module.finrank K (allTargetSourceSpan F) = h - 2 := by
  rw [allTargetSourceSpan_eq_pairSpan F hF hh]
  exact pairSpan_finrank F hF

end OAI.ExactFourier.PairTargetFrameLocal
