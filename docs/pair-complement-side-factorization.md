# Pair/complement side factorization (research candidate)

This is a scalar and binary-span audit for a side-wire compression.  It is
not yet a complete replacement for the eight-row circuit: the gate schedule,
arbitrary-auxiliary restoration, and every stage boundary still need Lean
formalization.

For a source triple \(T\), target triple \(S\), and \(r=|S\cap T|\), define
two pair aggregates for every unordered pair \(F\):

\[
 A_F(x)=\sum_{T\supset F}x_T,\qquad
 B_F(x)=\sum_{T\cap F=\varnothing}x_T .
\]

For the target \(S\), use \(A_F\) only when \(F\subset S\), and use \(B_F\)
only when \(F\cap S=\varnothing\).  Their coefficient counts on \(x_T\) are

\[
 M_2(r)=\binom r2,\qquad
 \bar M_2(r)=\binom{h-6+r}{2}.
\]

Writing \(c=h-6\), for \(h\ge7\),

\[
 \frac{M_2(r)-\bar M_2(r)}{2c}
   +\left(\frac12+\frac{c-1}{4}\right)
 =\frac{1-r}{2}.
\]

The right side is exactly the diagonal-free coefficient in the side moment:
it is \(+1/2,0,-1/2,-1\) for \(r=0,1,2,3\).  The last value is corrected
by the direct \(x_S\) term already present in the scalar invocation.  Thus
the candidate side correction is

\[
 \frac1{2(h-6)}
 \left(\sum_{F\subset S} A_F-\sum_{F\cap S=\varnothing}B_F\right)
 +\frac{h-5}{4}\,q,
 \qquad q=\sum_Tx_T .
\]

The global \(q\) is already in the span of the \(h\) shifted centre wires
when \(h\ne9\): if \(c_i=a_i-q/3\), then
\(\sum_i c_i=(3-h/3)q\).  Therefore this identity uses two pair banks
(\(2\binom h2\) scalar roles) and the existing \(h\) centre roles.

For each fixed pair \(F\), both source and target support families have the
same binary label span of dimension \(h-2\):

* \(A_F\): indicators of triples containing \(F\);
* \(B_F\): indicators of triples disjoint from \(F\).

The script checks the ranks over \(\mathbf F_2\) at \(h=7,8,24\).  The
row-5 target complements \(t_S^\perp\) in either target family generate the
full \(D\), as required if the aggregate is returned to the stage output
frame.

For row 0, the target lines add no extra dimension: if \(F\subset S\), then
\(t_S\) is in the span of the \(A_F\) labels; if \(F\cap S=\varnothing\),
then \(t_S\) is in the span of the \(B_F\) labels.  The remaining conditional
step is the shared row-2/row-5 gate and the restoration schedule, not a scalar
rank mismatch at row 0.

A conditional residual accounting explains why this candidate avoids the
earlier all-target pair-span charge.  In stage \(j\), let
\(e=h^{j-1}\), \(P\) be the prefix line, and \(B=P^\perp\), so
\(\dim B=e-1\).  If an aggregate support has span \(L\) of rank \(r_L\),
assign

\[
\begin{array}{c|c}
\text{edge} & \text{residual dimension}\\ \hline
0\to\text{row 0} & (e-1)r_L\\
\text{row 0}\to\text{row 2} & (e-1)(h-r_L)+r_L\\
\text{row 2}\to\text{row 5} & h-r_L\\
\text{row 5}\to\text{row 7} & 0 .
\end{array}
\]

The sum is \(eh\), exactly the same as one original pair-specific side role.
For the candidate \(r_L=h-2\), this becomes

\[
((e-1)(h-2),\;2(e-1)+h-2,\;2,\;0).
\]

This is a **conditional label construction**: it assumes the shared aggregate
can be touched by all target gates in its support family while preserving the
displayed nested labels.  It does not yet prove that the scalar gate map and
the complete three-stage route satisfy this assumption.

## h=24 arithmetic

With \(v=\binom{24}{3}=2024\), \(N_0=v^3=8,291,469,824\),
\(I_0=3v^2=12,289,728\), and \(m=24^3=13,824\),

\[
W_{\rm cand}
 =2N_0+I_0\left(2\binom{24}{2}+24\right)
 =23,661,822,976.
\]

The next power-of-two width is \(2^{35}=34,359,738,368\).  Keeping the
existing centre loss gives

\[
\Delta=2N_0-2I_0\,24^2=2,425,172,992,
\]
and the conditional normalized saving is

\[
\frac{\Delta}{m2^{35}}
 =\frac{2,368,333}{463,856,467,968}
 \approx 5.105745340525\times10^{-6}.
\]

This clears the \(10^{-9}\) target by several orders of magnitude **if** the
conditional frame and gate assumptions can be completed.  The original
side-role count per invocation is \(v\,d_{\rm nbr}=2,819,432\); the candidate
uses \(2\binom{24}{2}=552\), a factor \(528901/361\approx1464.8\) reduction.

Reproduce all scalar, rank, and arithmetic checks with:

\`\`\`bash
python3 scripts/pair_complement_side_audit.py
\`\`\`

The next formalization step is to instantiate the scalar map over the existing
\`CompressedInvocation\` interface with the two pair banks and prove that the
row-0/row-5 target partitions have the stated support spans.  Until that is
done, report the \(5.1057\times10^{-6}\) value as a research candidate, not
as a proved Fourier circuit.
