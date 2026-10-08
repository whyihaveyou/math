# Fixed-width gate schedule interface

`FixedWidthScheduleInterface.lean` adds the finite bridge between the
frame/event ledger and the repository's existing `Program`/`LinearDAG`
semantics.

`FixedWidthGateSchedule I h n a Frame Step` contains:

- a `LinearDAG n a`, whose `size` is the charged scalar gate count;
- an event label for every finite schedule step and a proof that all
  `Bool × Fin 3 × (Fin I × Fin h)` events are covered;
- an equivalence from the external `Step` type to the actual topological gate
  slots `Fin dag.size`;
- a frame state at every boundary between consecutive gate slots;
- a frame action for each dependent-width `Gate`, together with a trace law
  using the actual `Program.gateAt` gate at that slot.

The new `Program.gateAt` definition exposes the gate stored at a program slot
with its exact width `Gate (n + 1 + i)`.  This avoids replacing the dependent
`Program` semantics by an unrelated list of gates.

For H24, the theorem
`fixed_width_margin_gt_one_e_minus_nine` takes only the concrete gate-count
upper bound

```text
dag.size ≤ 6 * (I * h)
```

and derives the existing `10⁻⁹` normalized margin.  The proof obtains
`Fintype.card Step = dag.size` from the slot equivalence, constructs the
existing `ThreeStageReturnSchedule`, and invokes the six-phase margin theorem.

The bridge makes the remaining gap precise.  A scalar `LinearDAG` by itself
does not provide a frame state or a legal frame action for a complex gate, so
`gateFrameAction` and `frame_step` are explicit fields.  Instantiating those
fields with the eight-row complex gate, proving frame preservation/transport,
and proving the gate-count bound remain the physical implementation task.
The interface therefore does not claim a completed DFT circuit or an
all-length recurrence.
