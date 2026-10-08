import OAI.Computability.FourierCircuit.CenterBoundaryShearCandidate
import OAI.Computability.FourierCircuit.CenterBoundaryTensorProjection
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Schedule-level audit for the centre-boundary shear candidate

`CenterBoundaryShearCandidate` proves a local label repair: for a unit active
label `t` and a zero coordinate `w`, the involution
`unitCoordinateEquiv t w` sends `t` to a vector in `t^\perp`.  This file
separates that local fact from the physical eight-row schedule.

The first part defines a finite family of centre roles and records the exact
number of directional events, `I*h`.  The second part proves the corresponding
lower bound whenever a schedule is required to touch every role/direction
pair.  If the transport must be lifted and returned, the event type is
`Bool × (Role × Direction)`, giving the strict lower bound `2*I*h`.  A
three-stage schedule gives `3*I*h` forward events, or `6*I*h` with return.

These are bounds for an explicitly stated event model.  They do not claim
that a binary transvection is a legal complex gate.  A gate-level theorem
still needs a tensor lift, a frame-preserving eight-row insertion, and a
restoration/commutation law.  Those missing interfaces are recorded as
structures at the end of the file, so the conditional nature of the price is
machine-readable rather than hidden in an arithmetic definition.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryShearScheduleAudit

open CenterBoundaryShearCandidate
open CenterBoundaryTensorLift
open CenterBoundaryTensorProjection
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- One centre role carries a unit active target and a usable zero coordinate. -/
structure Role (h : ℕ) where
  target : Active h
  target_unit : dotProduct target target = (1 : F)
  witness : Fin h
  witness_zero : target witness = 0

/-- The local reversible transport attached to one role. -/
noncomputable def Role.transport {h : ℕ} (r : Role h) :
    Active h ≃ₗ[F] Active h :=
  unitCoordinateEquiv r.target r.witness r.target_unit r.witness_zero

@[simp] theorem Role.transport_target {h : ℕ} (r : Role h) :
    r.transport r.target = coordinate r.witness := by
  exact unitCoordinateEquiv_unit r.target r.witness
    r.target_unit r.witness_zero

theorem Role.transport_involutive {h : ℕ} (r : Role h) (x : Active h) :
    r.transport (r.transport x) = x := by
  exact r.transport.left_inv x

/-- The local shear really puts the direct inserted line in the old L5 row. -/
theorem Role.insert_transport_legal
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (hp : dotProduct p p = (1 : F)) (r : Role h) :
    insertP p (r.transport r.target) ∈ L5 p r.target := by
  exact sheared_insert_mem_L5 p r.target hp r.target_unit
    r.witness r.witness_zero

/-- The elementary event index: one active direction for one role. -/
abbrev Event (I h : ℕ) := Fin I × Fin h

@[simp] theorem event_card (I h : ℕ) :
    Fintype.card (Event I h) = I * h := by
  simp [Event]

/-- A schedule whose every event is assigned to one role/direction pair. -/
structure DirectionalSchedule (I h : ℕ) (Step : Type*) [Fintype Step] where
  touch : Step → Event I h
  complete : Function.Surjective touch

/-- Touching every role/direction pair costs at least `I*h` steps. -/
theorem directional_schedule_lower_bound
    {I h : ℕ} {Step : Type*} [Fintype Step]
    (s : DirectionalSchedule I h Step) :
    I * h ≤ Fintype.card Step := by
  rw [← event_card I h]
  exact Fintype.card_le_of_surjective s.touch s.complete

/-- The one-event-per-direction schedule exists abstractly. -/
def exactDirectionalSchedule (I h : ℕ) :
    DirectionalSchedule I h (Event I h) where
  touch := id
  complete := Function.surjective_id

@[simp] theorem exactDirectionalSchedule_card (I h : ℕ) :
    Fintype.card (Event I h) = I * h := by
  exact event_card I h

/-- A reversible lift-and-return event has a phase bit in addition to the
role/direction pair.  Surjectivity expresses that both forward and return
transport are actually scheduled, rather than merely being algebraically
available as an inverse. -/
abbrev ReturnEvent (I h : ℕ) := Bool × Event I h

@[simp] theorem return_event_card (I h : ℕ) :
    Fintype.card (ReturnEvent I h) = 2 * (I * h) := by
  simp [ReturnEvent, Event, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

structure ReturnSchedule (I h : ℕ) (Step : Type*) [Fintype Step] where
  touch : Step → ReturnEvent I h
  complete : Function.Surjective touch

/-- A genuine lift-and-return schedule has at least two directional units per
role, one in each phase. -/
theorem return_schedule_lower_bound
    {I h : ℕ} {Step : Type*} [Fintype Step]
    (s : ReturnSchedule I h Step) :
    2 * (I * h) ≤ Fintype.card Step := by
  rw [← return_event_card I h]
  exact Fintype.card_le_of_surjective s.touch s.complete

/-- Three independently scheduled forward stages. -/
abbrev StageEvent (I h : ℕ) := Fin 3 × Event I h

@[simp] theorem stage_event_card (I h : ℕ) :
    Fintype.card (StageEvent I h) = 3 * (I * h) := by
  simp [StageEvent, Event, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

structure ThreeStageSchedule (I h : ℕ) (Step : Type*) [Fintype Step] where
  touch : Step → StageEvent I h
  complete : Function.Surjective touch

/-- If each of the three address stages needs every directional event, the
forward schedule costs at least `3*I*h`. -/
theorem three_stage_schedule_lower_bound
    {I h : ℕ} {Step : Type*} [Fintype Step]
    (s : ThreeStageSchedule I h Step) :
    3 * (I * h) ≤ Fintype.card Step := by
  rw [← stage_event_card I h]
  exact Fintype.card_le_of_surjective s.touch s.complete

abbrev ThreeStageReturnEvent (I h : ℕ) := Bool × StageEvent I h

@[simp] theorem three_stage_return_event_card (I h : ℕ) :
    Fintype.card (ThreeStageReturnEvent I h) = 6 * (I * h) := by
  simp [ThreeStageReturnEvent, StageEvent, Event, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm]

structure ThreeStageReturnSchedule (I h : ℕ) (Step : Type*) [Fintype Step] where
  touch : Step → ThreeStageReturnEvent I h
  complete : Function.Surjective touch

/-- The corresponding lift-and-return lower bound for all three stages. -/
theorem three_stage_return_schedule_lower_bound
    {I h : ℕ} {Step : Type*} [Fintype Step]
    (s : ThreeStageReturnSchedule I h Step) :
    6 * (I * h) ≤ Fintype.card Step := by
  rw [← three_stage_return_event_card I h]
  exact Fintype.card_le_of_surjective s.touch s.complete

namespace H24

abbrev I : ℕ := CenterCompression.H24.I0
abbrev h : ℕ := CenterCompression.H24.h

theorem directional_price_eq : I * h = 294953472 := by
  norm_num [I, h, CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

theorem return_price_eq : 2 * (I * h) = 589906944 := by
  rw [directional_price_eq]

theorem three_stage_price_eq : 3 * (I * h) = 884860416 := by
  rw [directional_price_eq]

theorem three_stage_return_price_eq : 6 * (I * h) = 1769720832 := by
  rw [directional_price_eq]

/-- Under the event model, the nominal one-direction price is exactly the
number used by the earlier conditional ledger. -/
theorem conditional_margin_one_direction :
    CenterBoundaryShearCandidate.H24.shearedFusionMargin =
      6849475072 := by
  exact CenterBoundaryShearCandidate.H24.shearedFusionMargin_eq

/-- Even a two-phase lift-and-return remains positive for the *arithmetic*
centre-fusion saving.  This says nothing about whether the phases can be
implemented by the eight-row gate; it only prevents an incorrect claim that
reversibility alone kills this particular ledger. -/
theorem fused_margin_after_return_positive :
    CenterBoundaryShearCandidate.H24.centreFusionSaving -
        (2 * (I * h) : ℤ) > 0 := by
  norm_num [CenterBoundaryShearCandidate.H24.centreFusionSaving,
    CenterBoundaryShearCandidate.H24.v, CenterBoundaryShearCandidate.H24.h,
    CenterCompression.H24.N0, I, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

/-- Three independent forward stages also leave a positive arithmetic margin;
this is a calculation only, not a global schedule theorem. -/
theorem fused_margin_after_three_stages_positive :
    CenterBoundaryShearCandidate.H24.centreFusionSaving -
        (3 * (I * h) : ℤ) > 0 := by
  norm_num [CenterBoundaryShearCandidate.H24.centreFusionSaving,
    CenterBoundaryShearCandidate.H24.v, CenterBoundaryShearCandidate.H24.h,
    CenterCompression.H24.N0, I, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem fused_margin_after_six_phases_positive :
    CenterBoundaryShearCandidate.H24.centreFusionSaving -
        (6 * (I * h) : ℤ) > 0 := by
  norm_num [CenterBoundaryShearCandidate.H24.centreFusionSaving,
    CenterBoundaryShearCandidate.H24.v, CenterBoundaryShearCandidate.H24.h,
    CenterCompression.H24.N0, I, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

def sixPhaseNormalized : ℚ :=
  ((CenterBoundaryShearCandidate.H24.centreFusionSaving -
      (6 * (I * h) : ℤ)) : ℚ) /
    ((CenterCompression.H24.m : ℚ) * CenterCompression.H24.Wstar)

theorem sixPhaseNormalized_eq :
    sixPhaseNormalized = 2624369 / 237494511599616 := by
  norm_num [sixPhaseNormalized,
    CenterBoundaryShearCandidate.H24.centreFusionSaving,
    CenterBoundaryShearCandidate.H24.v, CenterBoundaryShearCandidate.H24.h,
    CenterCompression.H24.N0, CenterCompression.H24.m,
    CenterCompression.H24.Wstar, I, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem sixPhaseNormalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < sixPhaseNormalized := by
  rw [sixPhaseNormalized_eq]
  norm_num

/-! A gate-level implementation can now discharge the remaining cost
    obligation by supplying an actual finite step type.  The lower bound from
    `ThreeStageReturnSchedule` says that a complete six-phase schedule needs
    at least `6 * (I * h)` events.  If a future construction also gives the
    matching upper bound, its realized cost is exactly the six-phase ledger
    and inherits the strict `10^-9` margin below. -/

def scheduleNormalizedMargin {Step : Type*} [Fintype Step] : ℚ :=
  ((CenterBoundaryShearCandidate.H24.centreFusionSaving -
      (Fintype.card Step : ℤ)) : ℚ) /
    ((CenterCompression.H24.m : ℚ) * CenterCompression.H24.Wstar)

theorem schedule_card_eq_six_phase
    {Step : Type*} [Fintype Step]
    (s : ThreeStageReturnSchedule I h Step)
    (hupper : Fintype.card Step ≤ 6 * (I * h)) :
    Fintype.card Step = 6 * (I * h) := by
  exact le_antisymm hupper (three_stage_return_schedule_lower_bound s)

theorem schedule_normalized_gt_one_e_minus_nine
    {Step : Type*} [Fintype Step]
    (s : ThreeStageReturnSchedule I h Step)
    (hupper : Fintype.card Step ≤ 6 * (I * h)) :
    (1 : ℚ) / 10 ^ 9 < scheduleNormalizedMargin (Step := Step) := by
  have hcard := schedule_card_eq_six_phase s hupper
  rw [scheduleNormalizedMargin, hcard]
  exact sixPhaseNormalized_gt_one_e_minus_nine

end H24

/-! ## Concrete local tensor-lift bridge

The active-factor lift and its projection/readout laws are proved in
`CenterBoundaryTensorLift` and `CenterBoundaryTensorProjection`.  The two
theorems below expose those results from this schedule audit, so the remaining
open obligation is no longer the existence of a local tensor lift.  What is
still missing is a legal complex gate realizing the binary transport, its
commutation with the eight-row scalar map, and one global schedule across all
prefix types.
-/

theorem concrete_prefix_tensor_lift_interface
    {ι : Type*} {h : ℕ} (p : ι → F) :
    Nonempty (CenterBoundaryTensorLift.PrefixTensorLiftInterface (h := h) p) := by
  exact ⟨CenterBoundaryTensorLift.interface p⟩

theorem concrete_lifted_shear_boundary
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (x t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0)
    (w : Fin h) (hw : t w = 0)
    (z : SideRowGeneralArbitrary.E ι h)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p x) :
    z + CenterBoundaryTensorLift.lift
        (BinaryTransvection.unitCoordinateEquiv t w ht hw)
        (CenterRowGeneral.insert p t) ∈
      SideRowGeneralArbitrary.L5 p t := by
  exact CenterBoundaryTensorProjection.lifted_sheared_readout_mem_L5
    p x t hp ht hxt w hw z hz

end CenterBoundaryShearScheduleAudit
end ExactFourier
end OAI
