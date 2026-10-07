# Frame-compatible parity-split target aggregate (conditional candidate)

`ParitySplitTargetAggregate` gives the exact scalar side correction for a target
triple `S` by splitting source triples `T` into the classes

\[
 |S\cap T|=0 \quad\text{and}\quad |S\cap T|=2,
\]

with readout `zeroAggregate(S,x)/2 - twoAggregate(S,x)/2`.  The new Lean file
[`ParityTargetAggregateFrameCandidate.lean`](../lean/OAI/Computability/FourierCircuit/ParityTargetAggregateFrameCandidate.lean)
checks the corresponding local frame fact.

For any `h` and target triple `S`, it defines the two sets of source indicator
labels and their `ZMod 2` spans.  The theorems
`zeroSourceSpan_le_targetBoundary` and `twoSourceSpan_le_targetBoundary` prove
that each span is contained in

```text
((ZMod 2) ∙ indicator S).orthogonalBilin FrameLabels.dotForm.
```

The proof is the parity observation that intersection cardinalities zero and
two are even, followed by
`FrameLabels.indicator_orthogonal_of_even`.  The combined span is also contained
in the same boundary by `paritySourceSpan_le_targetBoundary`.  This is a local
label certificate; it does not prove that the source aggregates can be formed
in the proposed gates, that their scalar maps commute with those gates, or that
the banks fit into one global DAG schedule.  Those are explicit parameters of
`PhysicalParitySplitPremise` and remain open premises.

## h=24 arithmetic

The zero-charge center margin is

```text
2,425,172,992 / (13,824 · 2^36)
  = 2,368,333 / 927,712,935,936
  ≈ 2.5528726702625 · 10^-6,
```

so it is strictly greater than `10^-9`.  Charging one active unit per target
aggregate costs

```text
I0 · v = 12,289,728 · 2,024 = 24,874,409,472,
```

leaving margin `-22,449,236,480`; this is already negative.  The separate
conditional two-unit arithmetic audit in
[`ParityTargetAggregateArithmetic.lean`](../lean/OAI/Computability/FourierCircuit/ParityTargetAggregateArithmetic.lean)
uses `2 · I0 · v = 49,748,818,944` and records effective margin
`-47,323,645,952`.  These charge calculations are conditional accounting
models, not lower bounds for redesigned schedules.

The candidate is therefore useful as a frame-compatibility certificate and a
sharp zero-charge/positive-charge threshold.  A physical improvement toward a
`10^-9` exponent still needs a construction with zero amortized residual charge
(or a different shared routing argument), plus scalar/gate commutation and a
verified all-length schedule.
