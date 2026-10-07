# Pair-bank cancellation support audit

The pair/complement candidate uses 3 target-contained aggregates

\[
A_F=\sum_{T\supset F}x_T
\]

and 210 target-disjoint aggregates

\[
B_F=\sum_{T\cap F=\varnothing}x_T
\]

for a fixed target triple `S`.  A possible frame repair is to replace these
213 values by linear combinations whose source support lies in
`t_S^perp`.  Such a combination must vanish on every source triple `T` with
`|S ∩ T|` odd.  This would let the row-5 gate stay inside the target's
orthogonal boundary without paying a prefix-direction return.

The exact finite audit in
[`scripts/pair_cancellation_support_audit.py`](../scripts/pair_cancellation_support_audit.py)
forms the aggregate incidence matrix `A`, the odd-intersection restriction
`M_odd`, and `y`, twice the diagonal-free side coefficient (`+1` for
`|S ∩ T|=0`, `-1` for `|S ∩ T|=2`).  It computes over `Q`:

\[
\operatorname{rank}(M_{odd})=211,\quad
\operatorname{rank}\begin{pmatrix}M_{odd}\\A\end{pmatrix}=213,\quad
\operatorname{rank}\begin{pmatrix}M_{odd}&0\\A&y\end{pmatrix}=214.
\]

The final strict inequality proves that no one-shot linear combination of
the existing 3+210 pair values both has even source support and equals the
diagonal-free side correction.  Independent modular checks at primes 3 and
1,000,003 return the same rank separation.  This rules out the simplest
cancellation repair; it does not rule out new bank coordinates, a
multi-stage copy schedule, or a redesigned boundary.

Run:

```bash
python3 scripts/pair_cancellation_support_audit.py
```
