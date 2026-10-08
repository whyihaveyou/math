# Pair-bank joint-gate barrier (h = 24)

`PairComplementJointGateJoin.lean` formalizes a local binary-label obstruction for the pair/complement side candidate.  For the target triple `{0,1,2}`, let

```text
J = pairSpan {0,1} ⊔ pairSpan {0,2} ⊔ pairSpan {1,2}.
```

The Lean theorem `h24_target_pair_join_eq_top` proves `J = ⊤` in
`(Fin 24 → ZMod 2)`.  The companion theorem
`h24_target_disjoint_pair_join_eq_top` gives the same full-join result for
three target-disjoint B-bank spans (`{3,4}`, `{3,5}`, and `{4,5}`).  The first
proof writes each coordinate basis vector as the
four-point identity

```text
e_i = 1_{i,a,b} + 1_{i,a,c} + 1_{i,b,c},
```

and places every triple indicator in one of the three target pair spans.  Thus
a single common frame that touches all three target-side `A_F` aggregates must
carry the full active factor, rather than the rank-22 frame of one fixed pair.

This is a route-specific label fact.  It does not give a lower bound for
arbitrary complex linear circuits, and it does not rule out the conditional
aggregate-wise schedule in `PairComplementAggregateBoundary.lean`, where each
pair bank keeps its own boundary.  The result therefore preserves the status
of the (5.1057\times10^{-6}) pair/complement number as a research candidate,
while eliminating the simpler shared-gate implementation.

## Conditional price

`PairComplementSharedJoinPrice.lean` turns this into an exact H24 ledger under
the explicit unit-charge model.  The six pair roles (three A plus three
selected B witnesses) incur

```text
2 × 12,289,728 invocations × 552 pair roles = 13,567,859,712
```

extra directional units when a rank-22 bank is replaced by a full rank-24
shared frame.  This exceeds the centre saving `2,425,172,992`, with certified
integer margin `−11,142,686,720`.  The conclusion is conditional on that
charge model; it is a design warning for the shared-gate route, not a general
complexity lower bound.
