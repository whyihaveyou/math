# Singleton-complement side grouping (conditional obstruction)

A target triple (S) has two even source classes.  Instead of the 210 pair
aggregates for the disjoint class, group by one outside singleton:

\[
 D_i(S)=\sum_{\substack{i\in T\\T\cap S=\varnothing}}x_T
 \quad(i\in S^c),
 \qquad
 E_2(S)=\sum_{|T\cap S|=2}x_T.
\]

Every disjoint source triple contains exactly three outside singletons, while
an (r=2) source occurs once in (E_2).  Therefore the exact scalar identity is

\[
 \operatorname{side}(S,x)=\frac16\sum_{i\notin S}D_i(S)-\frac12 E_2(S),
\]

with coefficients (+1/2,0,-1/2,0) for intersection sizes (0,1,2,3).
Every aggregate has source support in (t_S^\perp), so this is a genuinely
frame-compatible scalar candidate distinct from the pair one-shot and the
single two-class aggregate.

The exact GF(2) audit is in
[`scripts/singleton_complement_side_audit.py`](../scripts/singleton_complement_side_audit.py).
For (h=24), each (D_i) has 190 source labels and rank 20; their join has
rank 21.  The (E_2) class has 63 labels and rank 23.  The joint support rank
is 23, so the two families have codimensions 3 and 1 in the active 24-space.

The construction keeps 22 target-indexed side roles (21 (D_i)'s plus (E_2))
per target, giving

\[
 W=564{,}114{,}901{,}504,
 \qquad W<2^{40}=1{,}099{,}511{,}627{,}776.
\]

Before frame charges, the centre saving is
\(Δ=2{,}425{,}172{,}992\), with nominal normalized value
\(2{,}368{,}333/14{,}843{,}406{,}974{,}976\approx1.5955\times10^{-7}\).
Under the conditional existing-boundary ledger, even an optimistic joint
full-active-to-family-support-to-full charge pays
\(2I_0v(3+1)=198{,}995{,}275{,}776\).  The resulting effective margin is
\(-196{,}570{,}102{,}784\) (normalized
\(-191{,}962{,}991/14{,}843{,}406{,}974{,}976\)).  Treating the 21 (D_i)
roles separately is no cheaper.

This is a conditional obstruction for the current frame boundary.  It does
not rule out a sequential routing scheme that transports the singleton groups
without a full-frame excursion, or a redesigned invocation interface.

Reproduce the exact scalar, rank, and arithmetic checks with:

```bash
python3 scripts/singleton_complement_side_audit.py
```
