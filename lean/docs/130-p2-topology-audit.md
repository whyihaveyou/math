# Two-factor audit for the ordered-pair invocation

Let (v={h\choose3}), (d={h-3\choose3}+3(h-3)), and use two tensor
coordinates (D_0\otimes D_0), of dimension (m=h^2).  There are (N=v^2)
bank entries and (I=2v) invocations in the two monotone stages.  Keeping
the centre-compressed (h)-wire bank gives

\[
 W_2=2N+I(vd+h),\qquad
 \Delta_2=2N-2Ih^2.
\]

For example, at (h=17),
\[
 (v,d,N,I,W_2,2^{\lceil\log_2W_2\rceil},\Delta_2)
 =(680,406,462400,1360,376416720,2^{29},138720),
\]
and at (h=20) these are
\[
 (1140,731,1299600,2280,1902660000,2^{31},775200).
\]
The corresponding raw gaps (1-\log_{h^2}(h^2-
\Delta_2/2^{\lceil\log_2W_2\rceil})) are (1.577837534\cdot10^{-7}) and
(1.506229362\cdot10^{-7}), respectively.

These are not Fourier circuits.  The two scalar stages are

\[
 S(x,y)=(x,y+x), \qquad L(x,y)=(x-y,y),
\]

so (L S(x,y)=(-y,x+y)), whereas the exchange required by the terminal
frames is ((-y,x)).  The Lean file
`work/h24-lean/ResearchP2ShearMatrix.lean` proves over ℚ that no two
upper/lower elementary shears, even with arbitrary coefficients, equal the
rotation.

Adding the third upper shear as a stage cannot reuse the two-factor tensor
induction: after stage 2, (X) already has label (D_0\otimes D_0) and
(Y) has label (U_d^\perp), the terminal labels.  A valid conservative
stage-3 invocation sets every gate row to the full label (D).  It then
crosses (U_d^\perp\leftrightarrow D) before and after the target bank,
costing two residual dimensions for every exceptional bank pair, (2N) in
total.  Combining it with the two monotone stages gives
\[
 \Delta_{\mathrm{eff}}=\Delta_2-2N=-2Ih^2=-4vh^2<0.
 \]

The (2N) charge is also a dimension-only lower bound for this row topology,
not just the cost of the all-(D) assignment.  At the threshold `dim = m`,
mark a gate label by 1 exactly when it is the full space (D), and by 0
otherwise.  A residual edge contains at least one unit whenever this bit drops
from 1 to 0.  For a target (S), source (T), and side path, write the four
per-target/source row bits as
\[
 a_S=H_0(S),\quad b_T=H_2(T),\quad
 c_S=H_5(S),\quad e_T=H_7(T).
\]
The (Y_S) path has endpoint bits (0,0), the (X_T) path has endpoint bits
 (1,1), and the side auxiliary has endpoint bits (0,1).  If the (Y_S)
path has no drop then all its internal bits are 0; if the (X_T) path has no
drop then all its internal bits are 1.  Under both assumptions the side path
contains (0,0,1,0,1,1), hence has a drop.  Thus, for every neighboring pair,
\[
 \#\mathrm{drops}(Y_S)+\#\mathrm{drops}(X_T)
   +\#\mathrm{drops}(A_{S,T})\ge 1.
\]
The neighbor graph is (d)-regular, so its bipartite double cover has a
perfect matching.  Sum the inequality over that matching: each (Y) and (X)
path and each selected side path is counted once, giving at least (v)
drops per invocation, hence (2v) residual dimensions.  There are (v)
invocations in the third stage, so every such stage costs at least (2v^2=2N).
The all-(D) assignment attains the bound.

The tempting alternative of changing the exceptional (Y)-sink to (D),
then pointwise combining the two-stage outputs, still needs one
codimension-one (D\leftrightarrow U_d^\perp) directional kernel after the
combination: (q_{U_d^\perp}-q_D=[u_d\cdot x]\pmod4), an (i^{[u_d\cdot x]})
Walsh-conjugated phase, not a free translation.  The sink change itself costs
one more dimension, so the same (2N) penalty remains.  The translation-only
difference is (2[u_d\cdot x]), which is why the original sink is
(U_d^\perp).
