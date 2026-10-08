# Explicit six-phase event schedule

`CenterBoundaryExactEventSchedule.lean` instantiates the event model from
`CenterBoundaryShearScheduleAudit` with the identity schedule on
`ThreeStageReturnEvent I h`.  Every stage, return phase, centre role, and
active direction appears exactly once, so the event count is exactly
`6 * (I*h)`.  At `h=24` this is `1,769,720,832` events.

The module therefore applies the existing conditional analytic conversion and
proves the strict `10^-9` exponent-gap inequality for this explicit finite
event schedule.  This closes the event-level existential bookkeeping gap.

It does not claim that an event is a legal complex gate.  A physical result
still needs a gate realization for each event, a frame-preserving global DAG,
and the all-length exact DFT recurrence.  The witness should therefore be
read as a formal event ledger, not as an unconditional faster FFT algorithm.

Build from `lean/` with:

```bash
lake build OAI.Computability.FourierCircuit.CenterBoundaryExactEventSchedule
```
