# Side-moment frame audit

The scalar moment identity is

\[
 \mathrm{sideNoDiag}(S,x)
 =\frac{q-\sum_{i\in S}a_i}{2},\qquad
 \mathrm{sideAction}(S,x)=\mathrm{sideNoDiag}(S,x)+x_S,
\]
where \(q=\sum_Tx_T\) and \(a_i=\sum_{T\ni i}x_T\).  The \(q,a_i\)
moments can be folded into the existing \(h\) shifted centre wires, but the
remaining \(x_S\) term needs a direct diagonal channel in the
\`CompressedInvocation\` interface.

A direct diagonal bank has one role per source/target triple.  In the current
stage labels its row-2 source line must enter the row-4 \(B\otimes D\) centre
gate and later return to the full X frame for restoration.  The source line
therefore loses one prefix direction and regains it, charging two absolute
residual units per direct role and invocation.

At \(h=24\),

\[
\begin{aligned}
W_{\rm diag}
 &=2N_0+I_0(v+h)=41{,}752{,}302{,}592,\\
\text{padding}&=2^{36}=68{,}719{,}476{,}736,\\
2I_0v&=49{,}748{,}818{,}944,\\
\Delta&=2{,}425{,}172{,}992.
\end{aligned}
\]

The conditional effective margin is
\(-47{,}323{,}645{,}952\), normalized as

\[
-\frac{23{,}107{,}249}{463{,}856{,}467{,}968}
\approx-4.98155\times10^{-5}.
\]

Thus the scalar side-moment identity alone does not improve the current
frame-labelled circuit.  A positive route would need to implement the
diagonal \(x_S\) term through a different stage boundary or a direct channel
with no signed frame decrease.

Reproduce the arithmetic with:

\`\`\`bash
python3 scripts/side_moment_frame_audit.py
\`\`\`

This is a conditional audit of the existing labels, not a universal lower
bound on other circuit organizations.

