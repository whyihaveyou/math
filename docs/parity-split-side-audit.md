# Parity-split target aggregates (conditional audit)

A side candidate not covered by the single parity aggregate is to keep the
two nonzero intersection classes separate.  For each target triple (S), set
[
 a_0(S)=sum_{|Scap T|=0}x_T,qquad
 a_2(S)=sum_{|Scap T|=2}x_T.
]
The readout (a_0(S)/2-a_2(S)/2) has coefficient (+1/2,0,-1/2,0) for
intersection sizes (0,1,2,3), exactly the off-diagonal side correction (the
(r=3) source is (T=S) and is excluded).  The scalar identity is checked
for all (\binom{24}{3}^2) source/target pairs by
[`scripts/parity_split_side_audit.py`](../scripts/parity_split_side_audit.py).

For a fixed target (S={0,1,2}), exact GF(2) elimination gives:

| source class | count | label-span rank | contained in (t_S^\perp)? |
|---|---:|---:|---|
| (r=0) | 1330 | 21 | yes |
| (r=2) | 63 | 23 | yes |
| union | 1393 | 23 | yes |

The (r=0) labels live in the 21-dimensional coordinate subspace on
(S^c).  The (r=2) labels span the full 23-dimensional target hyperplane.
Splitting the classes therefore makes the frame geometry more explicit, but it
does not remove the full hyperplane from the (r=2) component.

The nominal role count is
[
 W=2N_0+I_0(2v+h)=66{,}626{,}712{,}064,
]
which lies below the (2^{36}=68{,}719{,}476{,}736) bucket.  Before frame
charges, the centre-only saving remains (2{,}425{,}172{,}992).

Under the explicit conditional boundary premise that each class aggregate
must leave the full active factor and return to its class span, the codimensions
are (3) and (1).  The one-way charge is
[
 I_0v(3+1)=99{,}497{,}637{,}888,
]
and a round trip costs (198{,}995{,}275{,}776).  The resulting margin is
(-196{,}570{,}102{,}784), normalized by (24^3 2^{36}) as
[
 -\frac{191962991}{927712935936}\approx-2.06921\times10^{-4}.
]
Even the one-way charge already exceeds the centre saving.  This is a
conditional obstruction for the one-aggregate-per-target schedule; it does
not rule out sequential routing, cancellation between class banks, or a new
stage boundary that transports both classes jointly.

Reproduce the exact scalar, GF(2), and arithmetic checks with:

```bash
python3 scripts/parity_split_side_audit.py
```
