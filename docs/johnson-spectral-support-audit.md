# Johnson spectral support audit for the side correction

This note checks a possible side-wire route that is different from pair
aggregation: diagonalize the side correction in the Johnson intersection
algebra and transport its harmonic spectral components.  The executable
certificate is [`scripts/johnson_spectral_support_audit.py`](../scripts/johnson_spectral_support_audit.py).
It uses exact integer structure constants and rational arithmetic.

Let (V) be the 3-subsets of ([24]), and let (B_r[S,T]=1) when
(|Scap T|=r).  For the centre-compressed invocation, twice the side map is
[
 M=B_0-B_2.
]
The exact Johnson multiplication table gives
[
 M^2=708B_0+935B_1+1162B_2+1393B_3,
]
and
[
 (M-1267I)(M+229I)(M-2I)=0.
]
The three spectral projectors, written in the same basis, are:

| projector | (B_0,B_1,B_2,B_3) coefficients | rank |
|---|---|---:|
| (P_{1267}) | ((1,1,1,1)/2024) | 1 |
| (P_{-229}) | ((-1/616,5/1848,13/1848,1/88)) | 23 |
| (P_2) | ((2/1771,-17/5313,-40/5313,250/253)) | 2000 |

The ranks follow exactly from the diagonal coefficient times (|V|=2024),
as these are idempotent symmetric matrices.  For a fixed target, the four
intersection classes have sizes (1330,630,63,1).  Every coefficient in every
projector is nonzero, so each projector has all (2024) entries in every row
and (4,096,576) nonzero matrix entries in total.  In particular, all three
projectors have a nonzero diagonal at every triple.

The original (M) has zero diagonal and no odd-intersection entries.  The
spectral expansion recovers that support only by cancellation: the weighted
diagonal coefficient is
[
 1267(1/2024)-229(1/88)+2(250/253)=0.
]
Thus a spectral/harmonic implementation cannot itself be a sparse legal side
bank under the published pairwise-even, distinct source/target rule.  It would
need cancellation between terms on the (r=1) and (r=3) channels and on the
diagonal, or a new frame transport that permits those channels.  This is a
conditional support obstruction for spectral factorization; it does not rule
out nonlinear circuits, a non-spectral sparse factorization, sequential
edge-wise routing, or a redesigned stage boundary.

The audit is exact and reproducible:

```bash
python3 scripts/johnson_spectral_support_audit.py
```
