# Eliminating the redundant global side moment

The side-moment factorization uses

\[
q=\sum_Tx_T,
\qquad a_i=\sum_{T\ni i}x_T,
\qquad
\operatorname{sideNoDiag}(S,x)=\frac{q-\sum_{i\in S}a_i}{2}.
\]

Every source triple contains exactly three coordinates, hence

\[
\sum_{i=0}^{h-1} a_i=3q.
\]

Over a characteristic-zero field, \(q\) is therefore redundant.  The new Lean
file `SideMomentRedundantGlobalAudit.lean` defines

\[
\widetilde{\operatorname{sideNoDiag}}(S,x)=
\frac{\frac13\sum_i a_i-\sum_{i\in S}a_i}{2}
\]

and proves that it equals the original diagonal-free side map.  The resulting
direct scalar identity remains exact after adding \(x_S\).

The Lean file also defines `eightRowsDirect`, a minimal algebraic extension of
the generic invocation interface with a direct map \(D:X\to X\) at the target
row, and proves arbitrary-bank restoration from
\(R G+J V+D=\mathrm{id}\).  This removes the need to copy all 2,024 source
coordinates into the side bank at the scalar interface level.  It is an
interface certificate only: no existing frame label certifies that this direct
row can be scheduled without a residual charge.

At \(h=24\), storing 24 incidence moments rather than \(q\) plus 24 moments
changes the width from

\[
2N_0+I_0(25+24)=17{,}185{,}136{,}320
\]

to

\[
W=2N_0+I_0(24+24)=17{,}172{,}846{,}592<2^{34}=17{,}179{,}869{,}184.
\]

This crosses one binary padding boundary.  The conditional width margin is

\[
\frac{2{,}425{,}172{,}992}{24^3\,2^{34}}
 =\frac{2{,}368{,}333}{231{,}928{,}233{,}984}
 \approx 1.0211491\times10^{-5}>10^{-9}.
\]

The finite incidence matrix has exact GF(2) rank 24, so the 24 retained
moments are independent at the label level.  This is a genuine scalar
width improvement over the previous 25-moment candidate and exceeds the
(h=20) primitive one-gate margin.  It does not yet prove a physical circuit:
the diagonal (x_S) term still needs a frame-compatible direct route.  Under
the existing direct-diagonal ledger its charge is

\[
2I_0v=49{,}748{,}818{,}944,
\qquad
\Delta_{\rm direct}=-47{,}323{,}645{,}952,
\]

so the corresponding normalized margin is negative.  A positive physical
result requires a new invocation boundary that applies the direct term from
the logical source line without paying that full round-trip bank charge.

The executable audit is
[`scripts/side_moment_redundant_global_audit.py`](../scripts/side_moment_redundant_global_audit.py).
The Lean result is an exact scalar/width certificate only; it makes no
all-length or complex-gate claim.

Run:

```bash
python3 scripts/side_moment_redundant_global_audit.py
cd lean
lake env lean OAI/Computability/FourierCircuit/SideMomentRedundantGlobalAudit.lean
```
