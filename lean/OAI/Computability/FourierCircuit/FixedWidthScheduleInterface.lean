import OAI.Computability.FourierCircuit.CenterBoundaryShearScheduleAudit
import OAI.Computability.FourierCircuit.LinearDAG

/-!
# Fixed-width gate schedules for the centre-boundary margin

This file is the finite interface between the abstract event ledger in
`CenterBoundaryShearScheduleAudit` and the existing `Program`/`LinearDAG`
semantics.  A `Program` has a dependent gate width at each step, so the
interface exposes the gate at a slot with that same dependent type.  A frame
trace supplies the state before and after every gate.  The trace is explicit:
the file does not silently infer frame legality from a scalar `LinearDAG`.

The resulting theorem turns a gate-count upper bound into the existing
six-phase normalized margin theorem.  It is a bookkeeping bridge only.  A
future physical implementation still has to instantiate `gateFrameAction` and
prove the supplied frame transition law for the actual complex gate.
-/

namespace OAI
namespace ExactFourier

open CenterBoundaryShearScheduleAudit

/-! ## Gate slots of a topologically ordered `Program` -/

namespace Program

/-- The gate emitted at a finite program slot, with its exact available-width
    type.  Earlier slots retain their original width; the final slot is the
    gate stored by the outer `step` constructor. -/
def gateAt {n : ℕ} : {k : ℕ} → Program n k → (i : Fin k) → Gate (n + 1 + i.val)
  | 0, .nil, i => Fin.elim0 i
  | _ + 1, .step p g, i =>
      Fin.lastCases g (fun j => gateAt p j) i

@[simp] theorem gateAt_step_last {n k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) :
    gateAt (.step p g) (Fin.last k) = g := by
  simp [gateAt]

@[simp] theorem gateAt_step_castSucc {n k : ℕ} (p : Program n k) (g : Gate (n + 1 + k))
    (i : Fin k) :
    gateAt (.step p g) i.castSucc = gateAt p i := by
  simp [gateAt]

end Program

namespace CenterBoundaryShearScheduleAudit

open CenterBoundaryShearScheduleAudit

/-! ## A finite `LinearDAG` trace with frame state -/

structure FixedWidthGateSchedule
    (I h n a : ℕ) (Frame Step : Type*) [Fintype Step] where
  /-- The scalar DAG whose `size` is the number of charged gate slots. -/
  dag : LinearDAG n a
  /-- Every external schedule step carries one three-stage/phase event. -/
  event : Step → ThreeStageReturnEvent I h
  complete : Function.Surjective event
  /-- Identifies external schedule steps with actual topological gate slots. -/
  slot : Step ≃ Fin dag.size
  /-- Frame state before and after each finite gate slot. -/
  frame : Fin (dag.size + 1) → Frame
  /-- The frame action supplied for the actual gate at a slot. -/
  gateFrameAction : {w : ℕ} → Gate w → Frame → Frame
  /-- The frame trace follows the actual gate stored in the `Program`. -/
  frame_step : ∀ j : Fin dag.size,
    frame j.succ = gateFrameAction (Program.gateAt dag.program j) (frame j.castSucc)

def toSchedule
    {I h n a : ℕ} {Frame Step : Type*}
    [Fintype Step]
    (S : FixedWidthGateSchedule I h n a Frame Step) :
    ThreeStageReturnSchedule I h Step :=
  { touch := S.event
    complete := S.complete }

theorem card_step_eq_dag_size
    {I h n a : ℕ} {Frame Step : Type*}
    [Fintype Step]
    (S : FixedWidthGateSchedule I h n a Frame Step) :
    Fintype.card Step = S.dag.size := by
  simpa using Fintype.card_congr S.slot

theorem gate_count_upper_to_step_upper
    {I h n a : ℕ} {Frame Step : Type*}
    [Fintype Step]
    {S : FixedWidthGateSchedule I h n a Frame Step}
    (hupper : S.dag.size ≤ 6 * (I * h)) :
    Fintype.card Step ≤ 6 * (I * h) := by
  rw [card_step_eq_dag_size S]
  exact hupper

namespace H24

theorem fixed_width_margin_gt_one_e_minus_nine
    {n a : ℕ} {Frame Step : Type*} [Fintype Step]
    (S : FixedWidthGateSchedule I h n a Frame Step)
    (hupper : S.dag.size ≤ 6 * (I * h)) :
    (1 : ℚ) / 10 ^ 9 < scheduleNormalizedMargin (Step := Step) := by
  apply schedule_normalized_gt_one_e_minus_nine (toSchedule S)
  exact gate_count_upper_to_step_upper hupper

end H24

/-! ## What the interface does and does not prove

`dag.program` and `Program.gateAt` make the frame trace refer to actual
topologically ordered `Gate` values, while `slot` makes the event count equal
to the charged `LinearDAG.size`.  The remaining implementation obligation is
the supplied `gateFrameAction` and `frame_step` proof.  The existing scalar
`LinearDAG` API has no canonical frame state or gate-to-frame action, so those
fields cannot be derived from a `LinearDAG` alone.
-/

end CenterBoundaryShearScheduleAudit
end ExactFourier
end OAI
