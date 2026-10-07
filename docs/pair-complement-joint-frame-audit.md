# Joint-gate obstruction for the pair/complement candidate

The scalar identity in [pair-complement-side-factorization.md](pair-complement-side-factorization.md)
is exact, but its optimistic frame table omitted a joint-gate effect.

Fix a target triple \(S\).  The candidate row-0/row-5 target gate uses

* three \(A_F=\sum_{T\supset F}x_T\) aggregates with \(F\subset S\);
* \(\binom{21}{2}=210\) \(B_F=\sum_{T\cap F=\varnothing}x_T\) aggregates with
  \(F\cap S=\varnothing\).

For every such \(F\), the all-triple source labels in the aggregate span a
22-dimensional pair space.  For \(A_F\), the support includes \(T=S\), so
\(t_S\) is not orthogonal to the span.  For \(B_F\), the support contains both
zero- and one-intersection triples, so it also contains a label with odd dot
product with \(t_S\).  Consequently neither span is contained in
\(t_S^\perp\).  The exact GF(2) check gives

\[
\operatorname{rank}(\langle t_T:F\subset T\rangle)=
\operatorname{rank}(\langle t_T:F\cap T=\varnothing\rangle)=22,
\]
and the join of the three \(A_F\) spans (or of all 210 \(B_F\) spans) has
rank 24.

In the existing stage labels, the outgoing target frame at row 5 is

\[
 U_S=(B\otimes D)\perp(P\otimes t_S^\perp).
\]

A shared row-5 gate for any of these aggregates must contain the aggregate's
\(P\)-component and \(P\otimes t_S^\perp\).  Since the aggregate span is not
contained in \(t_S^\perp\), their join contains \(P\otimes D\).  The target
must therefore rise to \(E\otimes D\) for the gate and then return to \(U_S\),
losing one prefix direction.  Replacing the signed change by an absolute
residual charges two directional units per target and invocation.

At \(h=24\),

\[
 2I_0v
 =2\cdot12{,}289{,}728\cdot2024
 =49{,}748{,}818{,}944.
\]

The existing centre saving is only

\[
 \Delta=2{,}425{,}172{,}992,
\]
so the conditional effective margin becomes
\(-47{,}323{,}645{,}952\), with normalized value

\[
-\frac{23{,}107{,}249}{231{,}928{,}233{,}984}
\approx-9.9631\times10^{-5}.
\]

Thus the \(5.1057\times10^{-6}\) arithmetic candidate does not survive the
explicit common-row-5-frame premise.  Restricting every aggregate to even
intersection source triples makes its span lie inside \(t_S^\perp\), but then
the target-restricted rank deficits produce the separate conditional
\(5.186\times10^9\) penalty in \`frame-compatible-side-search.md\`, already
larger than \(\Delta\).

This is a conditional obstruction for the current eight-row boundaries; it is
not a lower bound for a redesigned network that changes the target boundary,
uses a different gate decomposition, or transports nonorthogonal aggregates
through another bank.

