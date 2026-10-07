# Target-aware even-pair side grouping (conditional audit)

This note records a finite search result for a possible side-wire compression.
It is a scalar and frame-dimension audit; it is not a verified circuit or an
all-length theorem.  The executable source is
[`scripts/frame_compatible_side_search.py`](../scripts/frame_compatible_side_search.py).

For a target triple (S), the original side correction uses only source
triples with (|S\cap T|=0) or (2).  Group a disjoint source triple by one of
its three pairs in (S^c), and group an intersection-two source triple by its
unique pair in (S).  The groups are

\[
 C_0=\{F:|F|=2, F\cap S=\varnothing\},\qquad
 C_2=\{F:F\subset S\},
\]

with (|C_0|=\binom{21}{2}=210) and (|C_2|=3).  The third coordinate is
restricted to remain outside (S).  This restriction matters: an unrestricted
disjoint pair also contains the (|S\cap T|=1) sources, which have zero side
coefficient.

The exact scalar weights are (+1/6) for each (C_0) aggregate and
(-1/2) for each (C_2) aggregate.  A disjoint source contains three (C_0)
pairs and an intersection-two source contains one (C_2) pair, so the weights
give (+1/2) and (-1/2), respectively.  The script checks this coefficient
identity for every one of the 2,024 triples at (h=24), with the target triple
itself excluded.

The exact GF(2) frame ranks are:

| object | rank |
|---|---:|
| all third coordinates through a fixed pair (F) | (h-2=22) |
| (C_2) target-restricted source span for one (F) | (h-3=21) |
| (C_0) target-restricted source span for one (F) | (h-5=19) |
| join of all (C_2) restricted spans | (23) |
| join of all (C_0) restricted spans | (21) |

Adding the target line to either individual restricted span adds one active
direction.  These dimensions are computed by exact Gaussian elimination over
(mathbb F_2), not floating point arithmetic.

The grouped role count is

\[
 W_{\rm even}=2N_0+I_0(213+h)=19{,}495{,}605{,}184,
\]

so the next power-of-two padding remains (2^{35}).  With the existing
centre saving (Δ=2{,}425{,}172{,}992), an **optimistic conditional** charge of
two directional units per grouped pair gives

\[
 2\binom{24}{3}^2(213)=1{,}745{,}141{,}376,
 \quad
 \Delta_{\rm opt}=680{,}031{,}616,
\]

and normalized margin

\[
 \frac{\Delta_{\rm opt}}{24^3\,2^{35}}
 =\frac{5{,}312{,}747}{3{,}710{,}851{,}743{,}744}
 \approx 1.43168\times 10^{-6}.
\]

This is a promising *arithmetic target*, not an achieved exponent improvement.
It also fails the stronger no-target-dependent-accumulation requirement: the
source filter ``|T∩S|=0`` or ``2`` is part of each aggregate definition.  A
target-independent pair bank must retain all 276 pairs and cancel the
intersection-one contributions, which is the separate all-pair audit and its
corrected negative margin.
The rank audit exposes the missing frame obligation.  If each group must leave
its shared (22)-dimensional pair span and return to its restricted span, a
two-direction-per-codimension accounting gives codimensions (3) for (C_0)
and (1) for (C_2).  The resulting conditional penalty is

\[
 2\binom{24}{3}^2(210\cdot3+3\cdot1)=5{,}186{,}265{,}216,
 \Delta_{\rm codim}=-2{,}761{,}092{,}224.
\]

This is larger than Δ and reverses the margin.
The precise gate labels and edge telescoping for this grouped route have not
been constructed, so neither cost model is a universal lower bound.  A valid
improvement would need to realize the two-unit charge without paying the
target-restricted codimensions, or use a different shared frame.

Run:

```bash
python3 scripts/frame_compatible_side_search.py
```

The script prints all integers and reduced rational margins used above.
