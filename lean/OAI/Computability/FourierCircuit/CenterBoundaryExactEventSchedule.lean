import OAI.Computability.FourierCircuit.CenterBoundaryShearScheduleAudit
import Mathlib.Tactic

/-!
# Explicit event-level witness for the six-phase centre ledger

`CenterBoundaryShearScheduleAudit` defines the required event type and proves
the lower bound for any schedule that touches every stage/phase/role/direction
event.  This file supplies the canonical identity schedule on that finite
event type.  It therefore proves the exact event-cardinality ledger and the
conditional `10^-9` exponent margin without leaving the event schedule as an
existential placeholder.

The witness is intentionally only an event-level schedule.  Its events are
not yet compiled to legal complex gates, a global frame-labelled DAG, or an
all-length exact DFT recurrence.
-/

namespace OAI
namespace ExactFourier
namespace CenterBoundaryExactEventSchedule

open CenterBoundaryShearScheduleAudit

abbrev Event (I h : ℕ) := ThreeStageReturnEvent I h

/-- The canonical schedule that executes each required event exactly once. -/
def exact (I h : ℕ) : ThreeStageReturnSchedule I h (Event I h) where
  touch := id
  complete := Function.surjective_id

@[simp] theorem exact_card (I h : ℕ) :
    Fintype.card (Event I h) = 6 * (I * h) := by
  exact three_stage_return_event_card I h

@[simp] theorem exact_complete (I h : ℕ) :
    Function.Surjective (exact I h).touch := by
  exact (exact I h).complete

namespace H24

abbrev I : ℕ := CenterBoundaryShearScheduleAudit.H24.I
abbrev h : ℕ := CenterBoundaryShearScheduleAudit.H24.h

theorem exact_card_eq :
    Fintype.card (Event I h) = 1769720832 := by
  rw [exact_card]
  exact CenterBoundaryShearScheduleAudit.H24.three_stage_return_price_eq

theorem exact_schedule_normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 <
      CenterBoundaryShearScheduleAudit.H24.scheduleNormalizedMargin
        (Step := Event I h) := by
  apply CenterBoundaryShearScheduleAudit.H24.schedule_normalized_gt_one_e_minus_nine
    (exact I h)
  rw [exact_card]

end H24
end CenterBoundaryExactEventSchedule
end ExactFourier
end OAI
