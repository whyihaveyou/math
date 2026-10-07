# h=24 all-pair class-price threshold

For one fixed target triple, the 276 pair labels split into 210 pairs with
zero target intersection, 63 with one target coordinate, and 3 contained in
the target. If their directional prices are `c0`, `c1`, and `c2`, the
per-target weighted count is

```text
210*c0 + 63*c1 + 3*c2.
```

`AllPairClassArithmeticH24.lean` formally checks these counts and the
associated integer arithmetic. Treating the weighted count as an already
amortized charge, a value at most 473 leaves a normalized margin above
`10^-9` under the fixed `2^45` denominator. This is a design threshold, not
an implementation result.

A target-indexed physical bank must multiply the count by the 2,024 target
triples. The same Lean file records the resulting stress tests:

- two units for every class gives family margin `-4,574,466,169,856`;
- even a single unit charged only to the three contained pairs gives family
  margin `-22,449,236,480`.

Thus the threshold cannot be used to claim an all-pair circuit improvement.
It identifies the amount of sharing or amortization a future frame-compatible
design must prove.
