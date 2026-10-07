import OAI.Computability.FourierCircuit.GroupedMomentSpan
import OAI.Computability.FourierCircuit.FrameLabels
import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# A finite-dimensional boundary charge for grouped side moments

`GroupedMomentSpan` shows that grouping singleton incidence moments over at
least two coordinates has full active-factor span.  This file connects that
label fact to the smallest possible round-trip charge at a triple boundary:
if a common gate label contains such a grouped source span, it is the full
active space, while the target side boundary is a codimension-one hyperplane.
A rise to the common label and a return therefore cost at least two residual
directions.

The result is deliberately local.  It does not assert that every side bank
must use a grouped moment or that no redesigned routing can avoid the
hypothesis.  It gives a precise conditional lower bound that a proposed
frame-compatible side compression must beat.
-/

namespace OAI
namespace ExactFourier
namespace GroupedMomentFrameCost

open FrameLabels
open GroupedMomentSpan

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- The target side boundary for a weight-three indicator. -/
def targetBoundary {h : ℕ} (T : Finset (Fin h)) :
    Submodule F (Active h) :=
  ((F ∙ indicator T).orthogonalBilin (dotForm : _))

/-- The directional charge of a nested edge, expressed only in dimensions. -/
noncomputable def residualCost {h : ℕ} (U V : Submodule F (Active h)) : ℕ :=
  Module.finrank F V - Module.finrank F U

/-- A common label containing a grouped singleton span is already full. -/
theorem common_label_eq_top {h : ℕ} (hh : 4 ≤ h)
    (C : Finset (Fin h)) (hC : 2 ≤ C.card)
    (J : Submodule F (Active h))
    (hJ : GroupedSpan C ≤ J) : J = ⊤ := by
  have hspan : GroupedSpan C = ⊤ := groupedSpan_eq_top hh C hC
  apply top_unique
  simpa [hspan] using hJ

/-- A triple boundary has exactly one fewer dimension than the active factor. -/
theorem targetBoundary_codim_one {h : ℕ}
    (T : Finset (Fin h)) (hT : T.card = 3) :
    Module.finrank F (targetBoundary T) + 1 = h := by
  have hc := triple_line_is_complement T hT
  have hs := Submodule.finrank_add_eq_of_isCompl hc
  have hn : indicator T ≠ 0 := by
    intro hz
    have hnorm := indicator_triple_norm T hT
    rw [hz] at hnorm
    simp at hnorm
  have hs' := hs
  rw [finrank_span_singleton hn] at hs'
  change Module.finrank (ZMod 2)
    (((ZMod 2) ∙ indicator T).orthogonalBilin (dotForm : _)) + 1 = h
  simpa [add_comm] using hs'

/-- Any grouped source label and a triple boundary require two directions for
one full round trip through the common label. -/
theorem roundtrip_cost_at_least_two {h : ℕ}
    (hh : 4 ≤ h) (C T : Finset (Fin h))
    (hC : 2 ≤ C.card) (hT : T.card = 3)
    (J : Submodule F (Active h))
    (hJ : GroupedSpan C ≤ J) :
    2 ≤ residualCost (targetBoundary T) J +
      residualCost (targetBoundary T) J := by
  have htop : J = ⊤ := common_label_eq_top hh C hC J hJ
  have hdim := targetBoundary_codim_one T hT
  have hfull : Module.finrank F (Active h) = h := by
    simp [Active, Module.finrank_pi]
  rw [htop]
  change 2 ≤
    (Module.finrank F (⊤ : Submodule F (Active h)) -
        Module.finrank F (targetBoundary T)) +
      (Module.finrank F (⊤ : Submodule F (Active h)) -
        Module.finrank F (targetBoundary T))
  rw [finrank_top, hfull]
  omega

namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
/-- One two-direction round trip for each target in each invocation. -/
def groupedPenalty : ℕ := 2 * I0 * v
def groupedMargin : ℤ := (centreSaving : ℤ) - (groupedPenalty : ℤ)

theorem h_eq : h = 24 := by rfl

theorem groupedPenalty_eq : groupedPenalty = 49748818944 := by
  norm_num [groupedPenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem groupedMargin_eq : groupedMargin = -47323645952 := by
  rw [groupedMargin, centreSaving_eq, groupedPenalty_eq]
  norm_num

theorem groupedMargin_neg : groupedMargin < 0 := by
  rw [groupedMargin_eq]
  norm_num

/-- The conditional charge is already more than the centre saving. -/
theorem groupedPenalty_exceeds_saving : centreSaving < groupedPenalty := by
  rw [centreSaving_eq, groupedPenalty_eq]
  norm_num

end H24
end GroupedMomentFrameCost
end ExactFourier
end OAI
