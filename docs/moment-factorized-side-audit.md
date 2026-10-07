# Global/incidence moment side bank

The repository already contains an exact moment factorization in
`CenterMap.lean`. For source values (x_T), let

\[
q=\sum_Tx_T,\qquad a_i=\sum_{T\ni i}x_T,
\qquad c_i=a_i-q/3.
\]

The target readout

\[
R_S(c)=\frac12\sum_{i\in S}c_i
\]

has coefficient ((|S\cap T|-1)/2) on (x_T). Therefore the diagonal-free
side correction is (-R_S(c)+x_S): for (r=0,1,2,3), its coefficients are
(1/2,0,-1/2,0). The existing theorem
`CenterCompression.compressed_plus_side` proves this identity when the
even-intersection side map is kept as a separate map.

## Frame audit

At (h=24), the source labels of the global moment (q) are all
\(\binom{24}{3}=2024\) triple indicators and have GF(2) span rank 24. The
source labels in one incidence moment (a_i) have rank 23. A centered wire
(c_i=a_i-q/3) has a nonzero coefficient on every source triple, so its
label support is again the full rank-24 span. Even if the explicit (q) wire
is omitted, the three incidence supports used by one fixed target already
join to rank 24. The global wire (q) is read by all targets, and the row-5
target complements (t_S^\perp) over all 2024 triple targets have join rank
24. Thus a common row-5 gate for the moment bank is forced to the full active
factor (D) before any target-specific regrouping.

Under the current eight-row boundary ledger, this is the same conditional
full-frame rise-and-return charge as the source-indexed bank:

\[
  2I_0v=2\cdot12{,}289{,}728\cdot2024=49{,}748{,}818{,}944.
\]

This is a premise about the published row labels, not a lower bound for a
new schedule that changes the boundary or transports the moments through a
different frame.

## Width and scalar operations

If the side bank stores (q) and the 24 centered moments, it has 25 side
roles, in addition to the existing 24 center roles. The h=24 width ledger is
therefore

\[
W=2N_0+I_0(25+24)=17{,}185{,}136{,}320,
\qquad 2^{34}<W<2^{35}.
\]

The centre-only arithmetic saving remains
\(\Delta=2{,}425{,}172{,}992\), but after the conditional full-frame charge
it is

\[
\Delta_{\rm eff}=-47{,}323{,}645{,}952,
\qquad
\frac{\Delta_{\rm eff}}{24^3\,2^{35}}
=-\frac{23{,}107{,}249}{231{,}928{,}233{,}984}
\approx-9.9631\times10^{-5}.
\]

At the scalar DAG level, a naive realization can share the moments because
`LinearDAG` preserves every old value and its output relabeling/fanout is free.
For (h=24), it uses 2,023 additions for (q), (24\binom{23}{2}-24=6,048)
incidence additions, one shared scale and 24 shifts to form (c_i), then
three gates per target for the \(-\frac12(c_{i_1}+c_{i_2}+c_{i_3})\) readout and
one direct (x_S) add. The reproducible script reports 16,192 gates before
the final (y\)-row updates, or 18,216 including one (y)-update per target.

There is an interface caveat. `CompressedInvocation.eightRows` defines
`J : A →+ X`, so its side map may read only the side bank. The direct
(x_S) term is available as a read-only original input in `LinearDAG`, but
using it requires a gate-level extension (J':A\times X\to X) (or adding all
2024 source wires to the side bank). Adding those source wires destroys the
width saving; changing the invocation interface requires a new restoration
lemma. Hence the moment factorization is an attractive scalar candidate, but
it is not a frame-compatible eight-row circuit in the current formal
interface.

Reproduce the rank, width, and operation counts with:

```bash
python3 scripts/moment_factorized_side_audit.py
```

The script intentionally labels the frame conclusion as conditional and does
not assert a general lower bound.
