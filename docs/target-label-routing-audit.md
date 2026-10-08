# Four-singleton target-label cover and route ledger

For a target triple (S) and a singleton binary label (e_i),

\[
e_i\in t_S^\perp \quad\Longleftrightarrow\quad i\notin S.
\]

The Lean certificate [`TargetLabelCover.lean`](../lean/OAI/Computability/FourierCircuit/TargetLabelCover.lean)
proves that the four labels (e_0,e_1,e_2,e_3) hit every target boundary for
every (h\ge 4). Four is minimal: any three chosen coordinates can themselves
be extended to a target triple, and that target contains all three singleton
labels.

The exact finite audit is
[`scripts/target_label_routing_audit.py`](../scripts/target_label_routing_audit.py).
At (h=24), (v=\binom{24}{3}=2{,}024) and the target classes are:

| number of eligible labels | targets |
|---:|---:|
| 1 | 4 |
| 2 | 120 |
| 3 | 760 |
| 4 | 1,140 |

Each singleton is eligible for (inom{23}{3}=1{,}771) targets. A
deterministic least-loaded assignment uses four equal blocks of 506 targets.
This is a cover and assignment statement only; it does not construct the
gates that form or route a target aggregate.

## Conditional direction ledgers

The base scalar width is inherited from the 24 singleton-incidence candidate:

\[
W=17{,}172{,}846{,}592<2^{34},\qquad
\Delta=2{,}425{,}172{,}992.
\]

The script reports four explicitly named charge conventions. The three prefix
sizes contribute (1+24+24^2=601).

| ledger premise | route charge | margin | normalized margin |
|---|---:|---:|---:|
| free target-labelled selection | 0 | 2,425,172,992 | (2368333/231928233984\approx1.0211491\times10^{-5}) |
| four-block singleton switches | 3,606 | 2,425,169,386 | (\approx1.0211475\times10^{-5}) |
| full↔singleton once per block | 110,584 | 2,425,062,408 | (\approx1.0211025\times10^{-5}) |
| full↔singleton per target | 55,955,504 | 2,369,217,488 | (148076093/14843406974976\approx9.97588\times10^{-6}) |

The switch-only line charges two directional units for each of the three
switches between four singleton blocks. The block line charges
(2(h-1)) for a full-active-to-singleton round trip once for each block. The
per-target line charges the same excursion for every one of the 2,024 targets.
These are accounting premises, not consequences of the existing frame API.

If four frame slots are additionally charged as scalar roles, the width crosses
to (2^{35}); the per-target line still has normalized margin about
(4.98794\times10^{-6}). This sensitivity line is included to make the
padding assumption visible. The result does not prove a complex gate,
simultaneous target schedule, direct (x_S) formation, or an all-length DFT
recurrence. It only identifies the exact finite cover and the amount of route
charge a future frame-compatible construction must realize.

Reproduce the audit with:

```bash
python3 scripts/target_label_routing_audit.py
```
