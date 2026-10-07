# Separating the h=24 all-pair cost factors

The class split for one fixed target triple is

```text
zero intersection: 210
one intersection:   63
two intersections:    3
```

For class prices `(c0,c1,c2)`, define the fixed-target weight

```text
Q(c0,c1,c2) = 210*c0 + 63*c1 + 3*c2.
```

Summing the target-indexed readout over all `v=2024` targets gives
`v*Q`. The frame-slot block `B` is a separate quantity: if it counts
invocation slots that have already been indexed by target, it must not receive
another target factor. The additive ledger used here is therefore

```text
frame-slot charge       = B*Q
target-readout charge   = v*Q
separated ledger charge = B*Q + v*Q.
```

This decomposition is deliberately conditional. It does not identify the
correct physical value of `B`, and it does not prove that either charge can be
implemented by the current frame labels.

As a concrete check, with two units in every class, `Q=552` and `v*Q=1,117,248`.
At `B=v^2`, the separated ledger is `2,262,427,200`. Multiplying the entire
target-readout cost by the same `v^2` block gives `4,576,891,342,848`; that
number is retained only as an explicit nested-product stress test, not as a
physical all-pair cost.

The fixed-pair view gives the same target/pair incidence totals:

```text
fixed pair F: 1540 targets with |F∩S|=0,
               462 targets with |F∩S|=1,
                22 targets with |F∩S|=2.
```

Thus
`2024*(210,63,3) = 276*(1540,462,22)` componentwise. The Lean file proves
this identity for arbitrary natural class prices.

Compile the certificate with:

```bash
cd lean
lake env lean OAI/Computability/FourierCircuit/AllPairCostDecompositionH24.lean
```
