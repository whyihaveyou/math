# Pair-only direct-channel re-audit (h = 24)

This note closes the current pair/complement side-wire branch at the direct
channel.  It combines the existing exact Lean no-go statements with a fresh
integer re-audit of the h=24 charge threshold.  The conclusion is route
specific: it does not lower-bound arbitrary complex circuits.

## Algebraic obstruction

The pair/complement readout is target-symmetric in

\[
r=|S\cap T|.
\]

`PairComplementQuadraticNoDiag.no_diagonal_free_quadratic` proves that a
quadratic coefficient assembled from pair/complement and global moments which
has the required values at `r=0,1,2` is forced to have value `-1` at `r=3`.
The desired diagonal-free side correction has value `0` at `r=3`, so the
missing correction is exactly `x_S`.

`PairCubicDiagonalNoGo.side_eq_quadratic_add_diagonal` identifies that missing
piece with `choose(r,3)`, the identity on the triple source bank.  Its
`identity_factorization_finrank_lower_bound` theorem says that any linear
factorization of this correction through an auxiliary bank has rank at least
`v = binom(24,3) = 2024`.  The independent h=6 witness in
`PairScalarNoGo.no_left_inverse` also shows that pair moments plus a global
moment cannot have a left inverse, even allowing an arbitrary reconstruction
map.

For the q-free shared-incidence variant, `DirectChannelCancellationBudget`
proves the stronger pointwise statement: after the centre composite and the
side moment cancel, any map completing the identity is `D = id` on the whole
source bank.  Thus the direct route cannot be replaced by a lower-rank
factorization within that interface.

## Exact h=24 charge threshold

The pair/complement candidate has

\[
V=\binom{24}{3}=2024,\qquad
I_0=3V^2=12{,}289{,}728,
\]

and its uncharged centre saving is
`Δ = 2,425,172,992`.  The direct map is touched once for every target in
every invocation, hence the audited count is

\[
I_0V=24{,}874{,}409{,}472.
\]

The exact break-even average frame charge is therefore

\[
\frac{\Delta}{I_0V}
 =\frac{2{,}425{,}172{,}992}{24{,}874{,}409{,}472}
 =\frac{74}{759}
 <1.
\]

Under an integral directional-unit ledger, any charged direct coordinate
already makes the margin negative:

| charge per direct coordinate | charge | margin |
|---:|---:|---:|
| 0 | 0 | 2,425,172,992 |
| 1 (one way) | 24,874,409,472 | −22,449,236,480 |
| 2 (rise and return) | 49,748,818,944 | −47,323,645,952 |

For the pair candidate's `2^35` padding, the two-way normalized margin is

\[
 -\frac{23{,}107{,}249}{231{,}928{,}233{,}984}
 \approx -9.9631031\times10^{-5},
\]

and the one-way value is

\[
 -\frac{43{,}846{,}165}{927{,}712{,}935{,}936}
 \approx -4.7262643\times10^{-5}.
\]

Therefore the existing pair-only route has no nonnegative direct-channel
ledger once a direct coordinate is assigned even one directional unit.  The
uncharged line is only a scalar-width candidate; it does not constitute a
frame-compatible gate.  A positive result requires changing the invocation
boundary or gate model so that the direct identity is realized without this
integral charge, while also supplying the missing global schedule and complex
gate proof.

Reproduce the arithmetic with:

```bash
python3 scripts/pair_direct_channel_reaudit.py
```

The Lean no-go files are:

- [`PairComplementQuadraticNoDiag.lean`](../lean/OAI/Computability/FourierCircuit/PairComplementQuadraticNoDiag.lean)
- [`PairCubicDiagonalNoGo.lean`](../lean/OAI/Computability/FourierCircuit/PairCubicDiagonalNoGo.lean)
- [`PairScalarNoGo.lean`](../lean/OAI/Computability/FourierCircuit/PairScalarNoGo.lean)
- [`DirectChannelCancellationBudget.lean`](../lean/OAI/Computability/FourierCircuit/DirectChannelCancellationBudget.lean)
