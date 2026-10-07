# Source-indexed side bank audit

A source-indexed side bank replaces the ordered neighboring wires
\(A_{S,T}\) by one auxiliary for each source triple \(T\).  The row-2 source
update is then direct, and the nominal role count is

\[
W_{\rm source}=2N_0+I_0(v+h)=41{,}752{,}302{,}592,
\]
with padding \(2^{36}=68{,}719{,}476{,}736\).

The frame issue is at row 5.  Fix a source \(T\).  Its side bank is read by
all \(1{,}393\) target triples \(S\) with even intersection and \(S\ne T\).
The GF(2) ranks at \(h=24\) are

\[
\operatorname{rank}\langle t_S:S\sim T\rangle=23,\qquad
\operatorname{rank}\langle t_S^\perp:S\sim T\rangle=24.
\]

Thus no fixed proper prefix component contains all row-5 target complements.
Under the existing target boundary, a common full row-5 frame makes each
target wire rise to \(E\otimes D\) and return across the one-dimensional
prefix direction.  The conditional absolute-residual charge is

\[
2I_0v=49{,}748{,}818{,}944.
\]

This exceeds the centre saving
\(\Delta=2{,}425{,}172{,}992\), yielding

\[
\Delta_{\rm eff}=-47{,}323{,}645{,}952,\qquad
\frac{\Delta_{\rm eff}}{m2^{36}}
=-\frac{23{,}107{,}249}{463{,}856{,}467{,}968}
\approx-4.98155\times10^{-5}.
\]

Holding the source bank in its one-dimensional source frame instead would
require a separate rise and return for each neighboring target hyperplane,
which is more expensive than the common full-frame route.  Therefore this
source-indexed compression does not improve the current three-stage
frame-labelled construction under the stated premise.

The audit is reproducible with:

\`\`\`bash
python3 scripts/source_indexed_side_audit.py
\`\`\`

This is a conditional result for the published row-5 boundaries, not a
lower bound for a redesigned schedule.

