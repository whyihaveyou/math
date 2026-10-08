# Diagonal-excluded pair/complement side audit

The pair/complement readout carries one direct source coordinate (x_S) for
the diagonal term.  It is therefore natural to remove the target source
(T=S) from each side aggregate and ask whether the remaining labels fit a
smaller frame.

For the canonical target (S={0,1,2}), the exact finite GF(2) audit gives:

| bank and target relation | aggregates | labels after deleting (T=S) | rank |
|---|---:|---:|---:|
| (A_F), (F\subset S) | 3 | 21 | 21 |
| (B_F), (F\cap S=\varnothing) | 210 | 1539 | 22 |

The (A)-bank loses one rank because its labels through a fixed pair are an
independent family.  The (B)-bank does not lose rank: the other 1,539
disjoint triples still span the same 22-dimensional away submodule.  Joining
the target-local (A) families has rank 23, while joining the (B) families
has rank 24.  For a fixed pair (F), the union of all target-excluded
(A) spans recovers the full pair span of rank 22; the Lean theorem
`common_sourceSpan_eq_bot` also shows that their common intersection is zero.

The four-edge aggregate-wise boundary ledger remains (e h) even when the
local support rank is (h-3): the extra codimension appears in the next edge
and exactly cancels the apparent saving.  At (h=24), the three prefix sizes
(1,24,24^2) cost 14,424 directional units per aggregate.  The existing
pair/complement bank has 552 aggregates, hence a conditional three-stage
ledger of 7,962,048 units; one target touches 213 aggregates, or 3,072,312
units under the same accounting.

The scalar pair/complement width remains

\[
  W=23{,}661{,}822{,}976\le 2^{35},
  \qquad
  \frac{2{,}425{,}172{,}992}{24^3,2^{35}}
  =\frac{2{,}368{,}333}{463{,}856{,}467{,}968}
  \approx 5.1057453\times 10^{-6}>10^{-9}.
\]

This is a stronger side-wire candidate than the (h=20) primitive one-gate
ledger ((\approx1.182\times10^{-8})) only at the level of the explicit
conditional aggregate-wise boundary model.  It is not an unconditional DFT
improvement.  A physical result still needs a complex gate realizing both
pair banks, scalar/gate commutation, a global frame-preserving schedule, and
the all-length recursion.

The executable finite audit is
[`scripts/pair_complement_diagonal_excluded_audit.py`](../scripts/pair_complement_diagonal_excluded_audit.py),
and the Lean rank/ledger interface is
[`PairComplementDiagonalExcludedAudit.lean`](../lean/OAI/Computability/FourierCircuit/PairComplementDiagonalExcludedAudit.lean).

Run:

```bash
python3 scripts/pair_complement_diagonal_excluded_audit.py
cd lean
lake env lean OAI/Computability/FourierCircuit/PairComplementDiagonalExcludedAudit.lean
```
