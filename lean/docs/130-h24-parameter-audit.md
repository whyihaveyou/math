# Family-130 `h=24` parameter audit

This note records a reproducible finite-network audit of the family-130 exact
DFT recurrence. It is a research supplement, not a replacement for the
published all-length theorem.

## Checked finite candidate

For `h = 24`,

```text
v = 2024                 d_nbr = 1393
N0 = 8,291,469,824       I0 = 12,289,728
m = 13,824               W* = 2^45
W' = 34,666,930,287,616  Delta' = 2,425,172,992
epsilon' = 2368333 / 474989023199232
```

The inherited recurrence formula gives numerical exponent gap
`5.2296989632709109e-10`. The exact rational arithmetic is checked in the
centre-compression and frame-budget modules. This number remains conditional
on re-establishing the full `h=24` frame-labelled stage, recursive scheduling,
and the integer/bit interface.

## Formalized local interfaces

The Lean additions check the scalar centre identity, characteristic-two
transvection transport, the direct-sum decomposition
`y^perp = <x> ⊔ <x,y>^perp` for an orthogonal unit pair, pure-tensor line
inclusions, and a small `StageResidual.Certificate` interface. These files do
not assert a complete eight-row network or a new all-length theorem.

## Side-compression boundary audit

One aggregate per target triple has an exact scalar update and would reduce the
ordered role count algebraically. Under the existing common-frame gate and
stage-boundary conditions, each aggregate pays two extra one-dimensional
full-frame transitions. At `h=24` the exact penalty is
`2 I0 v = 49,748,818,944`, exceeding the centre saving and leaving effective
margin `-47,323,645,952`. The target aggregate is therefore a checked
obstruction for this architecture, not a positive complexity result.

See `TargetSideAggregate.lean` and
`ResearchTargetSideAggregateArithmetic.lean` for the scalar identity and
arithmetic obstruction.
