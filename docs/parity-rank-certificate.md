# h=24 parity-bank rank certificate

For the fixed target (S={0,1,2}), the parity-split source labels have the
following exact GF(2) ranks:

| bank | number of labels | rank |
| --- | ---: | ---: |
| (|S\cap T|=0) | 1330 | 21 |
| (|S\cap T|=2) | 63 | 23 |
| union | 1393 | 23 |

The first row is the coordinate space on the 21 coordinates outside (S).
For every outside coordinate (i), choose distinct (a,b,c) outside (Scup
{i}).  The three zero-bank labels satisfy

```text
1_{iab} + 1_{iac} + 1_{ibc} = e_i  (over GF(2)).
```

Thus the zero bank contains all 21 outside coordinate vectors, while every
zero-bank label vanishes on (S), giving rank 21.

For the two bank, write (p_{ij}=e_i+e_j) for a pair in (S).  Fix one
outside coordinate (k_0).  Differences of labels with the same (k_0)
give two independent target-even vectors, for example

```text
1_{01k0} + 1_{02k0} = e_1 + e_2,
1_{01k0} + 1_{12k0} = e_0 + e_2.
```

Their sum recovers (p_{01}).  For every outside (k),

```text
1_{01k} + p_{01} = e_k.
```

Consequently the two bank contains 21 outside basis vectors and a
two-dimensional target-even subspace, hence rank (21+2=23).  Every two-bank
label has even intersection with (S), so it lies in the 23-dimensional
target orthogonal complement; this proves that the rank is full inside that
complement.  The union cannot increase the rank.

The finite checks and witness identities are reproduced by:

```bash
python3 scripts/parity_rank_certificate.py
```

This is an auditable Python certificate, not a Lean rank theorem.  The Lean
file
[`ParityTargetAggregateFrameCandidate.lean`](../lean/OAI/Computability/FourierCircuit/ParityTargetAggregateFrameCandidate.lean)
currently proves the weaker but schedule-relevant span containment in the
target boundary.  Neither artifact proves source formation, scalar/gate
commutation, a global DAG, or an all-length DFT circuit.
