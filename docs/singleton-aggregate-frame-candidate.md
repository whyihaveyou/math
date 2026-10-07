# Singleton-incidence aggregate candidate (conditional)

The pair/complement route is not the only way to share side wires.  A smaller
scalar bank uses one incidence aggregate for each coordinate:

\[
A_i=\sum_{T\ni i}x_T,\qquad
q=\frac13\sum_iA_i.
\]

For a target triple (S), the diagonal-free side coefficient is

\[
\frac{q-\sum_{i\in S}A_i}{2},
\]

which gives ((1-r)/2) on a source triple with (r=|S\cap T|).  The
diagonal (r=3) coefficient is (-1), so a direct (x_S) channel is still
needed to close the scalar invocation.  The script
`scripts/singleton_aggregate_frame_search.py` checks these four intersection
classes with exact rationals.

At (h=24), each incidence support has GF(2) rank 23, while the three
incidence supports touched by a fixed target already join to rank 24.  The
rank-23 statement is the local aggregate premise; the rank-24 join is a
warning that a common target gate cannot be assumed for free.

Under the **conditional aggregate-wise ledger** that routes each incidence
aggregate separately, one rank-23 aggregate has the four edge prices

\[
((e-1)23),\quad ((e-1)1+23),\quad 1,\quad 0,
\]

whose sum is (24e).  Across prefix sizes (e=1,24,576), this is 14,424
direction units per aggregate and 346,176 for all 24 aggregates.

The nominal width uses 24 side roles and 24 compressed centre roles:

\[
W=17{,}172{,}846{,}592<2^{34}=17{,}179{,}869{,}184.
\]

Keeping the centre saving (Δ=2{,}425{,}172{,}992), the resulting conditional
normalized value is

\[
\frac{2{,}368{,}333}{231{,}928{,}233{,}984}
 \approx 1.0211491\times 10^{-5},
\]

which is formally above (10^{-9}) (and above (10^{-6})).  The side roles
per invocation fall from 2,819,432 to 24.

This is a research candidate only.  The script does not prove a complex gate
realizing the direct (x_S) channel, does not transport the 24 aggregates
through the target-family row-5 boundaries, and does not prove arbitrary
auxiliary restoration or the all-length recursion.  In particular, the
rank-24 target join shows why the aggregate-wise route remains an explicit
frame premise rather than an established circuit.

Reproduce the exact audit with:

```bash
python3 scripts/singleton_aggregate_frame_search.py
```
