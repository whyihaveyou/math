import OAI.Computability.FourierCircuit.ParitySplitTargetAggregate
import OAI.Computability.FourierCircuit.ParityTargetAggregateArithmetic
import OAI.Computability.FourierCircuit.FrameLabels
import OAI.Computability.FourierCircuit.FixedWidthScheduleInterface
import Mathlib.Tactic

/-!
# Frame-compatible parity-split target aggregates (conditional candidate)

Fix a target triple `S`.  The source triples with intersection cardinality
zero or two form two parity classes.  Every indicator in either class is
orthogonal to the target indicator, so the spans of the two banks lie in the
same target boundary (the orthogonal complement of the target line).

This is a label-level certificate.  It does not construct the physical source
formation, prove scalar/gate commutation, or provide a global DAG schedule.
Those facts are explicit premises for any future circuit-level compression.
The h=24 arithmetic records the zero-charge margin and the sharp obstruction
from charging one active unit per target aggregate.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace ParityTargetAggregateFrameCandidate

open CenterCompression
open FrameLabels

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- The zero-intersection source indicators for a fixed target triple. -/
def zeroSourceLabels {h : ℕ} (S : Triple h) : Set (Active h) :=
  {v | ∃ T : Triple h, (S.1 ∩ T.1).card = 0 ∧ v = indicator T.1}

/-- The two-intersection source indicators for a fixed target triple. -/
def twoSourceLabels {h : ℕ} (S : Triple h) : Set (Active h) :=
  {v | ∃ T : Triple h, (S.1 ∩ T.1).card = 2 ∧ v = indicator T.1}

/-- Spans of the two parity-selected source banks. -/
def zeroSourceSpan {h : ℕ} (S : Triple h) : Submodule F (Active h) :=
  Submodule.span F (zeroSourceLabels S)

def twoSourceSpan {h : ℕ} (S : Triple h) : Submodule F (Active h) :=
  Submodule.span F (twoSourceLabels S)

/-- The row-5 target boundary for the target indicator. -/
def targetBoundary {h : ℕ} (S : Triple h) : Submodule F (Active h) :=
  ((F ∙ indicator S.1).orthogonalBilin (dotForm : _))

private theorem even_of_card_zero {n : ℕ} (hn : n = 0) : Even n := by
  refine ⟨0, ?_⟩
  simpa [hn]

private theorem even_of_card_two {n : ℕ} (hn : n = 2) : Even n := by
  refine ⟨1, ?_⟩
  omega

private theorem targetBoundary_mem_of_even {h : ℕ}
    (S T : Triple h) (heven : Even (T.1 ∩ S.1).card) :
    indicator T.1 ∈ targetBoundary S := by
  rw [targetBoundary, Submodule.orthogonalBilin_span_singleton]
  change dotForm (indicator S.1) (indicator T.1) = 0
  exact indicator_orthogonal_of_even T.1 S.1 heven

/-- Every zero-intersection source indicator is legal at the target boundary. -/
theorem zeroSource_indicator_mem {h : ℕ} (S T : Triple h)
    (hzero : (S.1 ∩ T.1).card = 0) :
    indicator T.1 ∈ targetBoundary S := by
  apply targetBoundary_mem_of_even S T
  have hrev : (T.1 ∩ S.1).card = 0 := by
    simpa [Finset.inter_comm] using hzero
  exact even_of_card_zero hrev

/-- Every two-intersection source indicator is legal at the target boundary. -/
theorem twoSource_indicator_mem {h : ℕ} (S T : Triple h)
    (htwo : (S.1 ∩ T.1).card = 2) :
    indicator T.1 ∈ targetBoundary S := by
  apply targetBoundary_mem_of_even S T
  have hrev : (T.1 ∩ S.1).card = 2 := by
    simpa [Finset.inter_comm] using htwo
  exact even_of_card_two hrev

/-- The zero-intersection bank has a frame-compatible span. -/
theorem zeroSourceSpan_le_targetBoundary {h : ℕ} (S : Triple h) :
    zeroSourceSpan S ≤ targetBoundary S := by
  apply Submodule.span_le.2
  intro v hv
  rcases hv with ⟨T, hzero, rfl⟩
  exact zeroSource_indicator_mem S T hzero

/-- The two-intersection bank has a frame-compatible span. -/
theorem twoSourceSpan_le_targetBoundary {h : ℕ} (S : Triple h) :
    twoSourceSpan S ≤ targetBoundary S := by
  apply Submodule.span_le.2
  intro v hv
  rcases hv with ⟨T, htwo, rfl⟩
  exact twoSource_indicator_mem S T htwo

/-- Their combined span is still contained in the same target boundary. -/
theorem paritySourceSpan_le_targetBoundary {h : ℕ} (S : Triple h) :
    zeroSourceSpan S ⊔ twoSourceSpan S ≤ targetBoundary S := by
  exact sup_le (zeroSourceSpan_le_targetBoundary S)
    (twoSourceSpan_le_targetBoundary S)

/-- Candidate-level premises still needed to turn the label fact into a circuit. -/
structure PhysicalParitySplitPremise (h : ℕ) (S : Triple h)
    (sourceFormation scalarGateCommutation globalSchedule : Prop) : Prop where
  source_formation : sourceFormation
  scalar_gate_commutation : scalarGateCommutation
  global_schedule : globalSchedule

/-- The parity banks can only be called a physical construction after these
premises are supplied; the present file intentionally does not prove them. -/
theorem physical_candidate_requires_premises {h : ℕ} (S : Triple h)
    {sourceFormation scalarGateCommutation globalSchedule : Prop}
    (P : PhysicalParitySplitPremise h S sourceFormation
      scalarGateCommutation globalSchedule) :
    sourceFormation ∧ scalarGateCommutation ∧ globalSchedule := by
  exact ⟨P.source_formation, P.scalar_gate_commutation, P.global_schedule⟩

namespace H24

open ParityTargetAggregateArithmetic

/-- The h=24 zero-charge arithmetic margin before any boundary charge. -/
def zeroCostMargin : ℤ :=
  (ParityTargetAggregateArithmetic.H24.delta : ℤ)

def zeroCostNormalized : ℚ :=
  (zeroCostMargin : ℚ) /
    ((CenterCompression.H24.m : ℚ) * (2 ^ 36 : ℚ))

/-- One active unit per target aggregate, in both parity banks. -/
def oneUnitPerTargetCharge : ℤ :=
  (ParityTargetAggregateArithmetic.H24.I0 * CenterCompression.H24.v : ℤ)

def oneUnitChargeMargin : ℤ :=
  zeroCostMargin - oneUnitPerTargetCharge

theorem zeroCostMargin_eq : zeroCostMargin = 2425172992 := by
  norm_num [zeroCostMargin, ParityTargetAggregateArithmetic.H24.delta,
    CenterCompression.H24.deltaCompressed,
    CenterCompression.H24.N0, CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem oneUnitPerTargetCharge_eq : oneUnitPerTargetCharge = 24874409472 := by
  norm_num [oneUnitPerTargetCharge,
    ParityTargetAggregateArithmetic.H24.I0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem oneUnitChargeMargin_eq : oneUnitChargeMargin = -22449236480 := by
  rw [oneUnitChargeMargin, zeroCostMargin_eq, oneUnitPerTargetCharge_eq]
  norm_num

theorem oneUnitChargeMargin_neg : oneUnitChargeMargin < 0 := by
  rw [oneUnitChargeMargin_eq]
  norm_num

theorem zeroCostNormalized_gt_one_e_minus_nine :
    zeroCostNormalized > (1 : ℚ) / 10 ^ 9 := by
  rw [zeroCostNormalized, zeroCostMargin_eq]
  rw [CenterCompression.H24.m_eq]
  norm_num

/-- The zero-charge normalized candidate is positive at the 1e-9 scale, while
one unit per target aggregate already crosses below zero under this charge
model.  These are arithmetic facts, not a physical schedule theorem. -/
theorem zero_cost_positive_one_e_minus_nine_and_one_unit_negative :
    zeroCostNormalized > (1 : ℚ) / 10 ^ 9 ∧ oneUnitChargeMargin < 0 := by
  exact ⟨zeroCostNormalized_gt_one_e_minus_nine,
    oneUnitChargeMargin_neg⟩

end H24

/-- A finite schedule attachment keeps the three unresolved implementation
premises explicit while linking them to an actual fixed-width DAG trace.
The gate-count hypothesis is intentionally supplied by the future physical
construction; no schedule is inferred from label containment alone. -/
structure FiniteScheduleAttachment
    {S : Triple 24}
    {sourceFormation scalarGateCommutation globalSchedule : Prop}
    (Frame Step : Type*) [Fintype Step]
    (n a : ℕ) where
  physical : PhysicalParitySplitPremise 24 S sourceFormation
      scalarGateCommutation globalSchedule
  schedule : CenterBoundaryShearScheduleAudit.FixedWidthGateSchedule
      CenterBoundaryShearScheduleAudit.H24.I
      CenterBoundaryShearScheduleAudit.H24.h n a Frame Step
  gate_upper : schedule.dag.size ≤
      6 * (CenterBoundaryShearScheduleAudit.H24.I *
        CenterBoundaryShearScheduleAudit.H24.h)

/-- Conditional attachment theorem for the parity candidate.  Once source
formation, scalar/gate commutation, and one global finite schedule are
provided, the existing fixed-width bridge yields the strict h=24 margin. -/
theorem finite_schedule_attachment_margin
    {S : Triple 24}
    {sourceFormation scalarGateCommutation globalSchedule : Prop}
    {Frame Step : Type*} [Fintype Step]
    {n a : ℕ}
    (A : FiniteScheduleAttachment (S := S)
      (sourceFormation := sourceFormation)
      (scalarGateCommutation := scalarGateCommutation)
      (globalSchedule := globalSchedule) Frame Step n a) :
    sourceFormation ∧ scalarGateCommutation ∧ globalSchedule ∧
      ((1 : ℚ) / 10 ^ 9 <
        CenterBoundaryShearScheduleAudit.H24.scheduleNormalizedMargin
          (Step := Step)) := by
  refine ⟨A.physical.source_formation,
    A.physical.scalar_gate_commutation,
    A.physical.global_schedule, ?_⟩
  exact CenterBoundaryShearScheduleAudit.H24.fixed_width_margin_gt_one_e_minus_nine
    A.schedule A.gate_upper

/-- The same attachment exposes the exact six-phase event ledger. -/
theorem finite_schedule_attachment_card
    {S : Triple 24}
    {sourceFormation scalarGateCommutation globalSchedule : Prop}
    {Frame Step : Type*} [Fintype Step]
    {n a : ℕ}
    (A : FiniteScheduleAttachment (S := S)
      (sourceFormation := sourceFormation)
      (scalarGateCommutation := scalarGateCommutation)
      (globalSchedule := globalSchedule) Frame Step n a) :
    Fintype.card Step =
      6 * (CenterBoundaryShearScheduleAudit.H24.I *
        CenterBoundaryShearScheduleAudit.H24.h) := by
  apply CenterBoundaryShearScheduleAudit.H24.schedule_card_eq_six_phase
    (CenterBoundaryShearScheduleAudit.toSchedule A.schedule)
  exact CenterBoundaryShearScheduleAudit.gate_count_upper_to_step_upper A.gate_upper

end ParityTargetAggregateFrameCandidate
end ExactFourier
end OAI
