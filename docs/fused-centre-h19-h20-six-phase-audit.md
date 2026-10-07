# h=19 and h=20 six-phase fused-centre audit

This snapshot extends the exact arithmetic ledger used by the h=16--18
comparison to the next two padding points.  Write

```text
v = C(h,3),       d = C(h-3,3) + 3(h-3),
N = v^3,          I = 3v^2,
W = 2N + I(vd+h+1),
P = next power of two above W,
S = 2N - 4v^2 h^2, Q = I h.
```

The six-phase ledger is `S - 6Q`, normalized by `h^3 P`.  The Lean file
`FusedCentreBoundaryArithmeticH19H20.lean` checks the following exact values:

| h | v | W | P | S | Q | S-6Q | normalized six-phase margin |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 19 | 969 | 1,661,448,297,294 | 2^41 | 463,846,734 | 53,520,777 | 142,722,072 | `2601/274877906944` |
| 20 | 1,140 | 3,252,070,954,800 | 2^42 | 883,728,000 | 77,976,000 | 415,872,000 | `3249/274877906944` |

Both normalized values are strictly larger than `10^-9`, and the h=20 value
is larger than h=19.  An independent exact scan of the same formulas gives
the conditional six-phase threshold interval h=18--37 for h up to 1000, with
h=20 the largest value in that scan (`≈1.18198·10^-8`).

These are arithmetic stress tests under an explicit event-count model.  They
do not construct a complex linear gate, prove scalar/gate commutation, supply
a frame-preserving global DAG, justify terminal role compression, or prove an
all-length DFT theorem.  In particular, the positive number is a research
candidate and must not be stated as a new unconditional exponent.
