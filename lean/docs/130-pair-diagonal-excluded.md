# Diagonal-excluded pair-prefix audit

This note isolates a potentially useful local geometry for compressing the
ordered side bank. It is a conditional research candidate; it is not a
frame-labelled stage or an all-length Fourier circuit.

For a pair F={i,j}, define the pair moment

    a_F = sum_{T containing F} x_T.

For a target S=F union {k}, remove the diagonal term x_S:

    a_{F,S} = a_F - x_S
             = sum_{T containing F, T != S} x_T.

At h=24, there are 22 source triples containing F, and 21 after removing S.
The reproducible script
[`scripts/pair_diagonal_excluded_audit.py`](../scripts/pair_diagonal_excluded_audit.py)
computes binary Gaussian elimination on the corresponding indicator vectors.
For every F subset S, it reports

| local set | number of vectors | rank over F2 | relation to t_S |
| --- | ---: | ---: | --- |
| `{t_T : T contains F}` | 22 | 22 | -- |
| `{t_T : T contains F, T != S}` | 21 | 21 | every vector is in `t_S`-perp |

The union of the three diagonal-excluded supports for the three pairs inside
S has rank 23, exactly the dimension of `t_S`-perp. Thus the
 diagonal-excluded local side edge has a clean finite-field interpretation: its
source support lies in the target orthogonal hyperplane, and the three pair
supports together span that hyperplane.

This local fact does **not** give a schedule. A physical aggregate `a_F` is
reused for many targets, while the subspace after removing `x_S` depends on S.
A complete construction must show how to accumulate the source values, change
the aggregate frame, and read the three pair moments at a target without paying
those transitions repeatedly. In particular, the rank check does not justify
treating one pair wire as simultaneously carrying all `a_{F,S}`.

## Conditional arithmetic

Ignoring that unresolved reuse problem, suppose a pair-prefix implementation
uses one aggregate for each of the 276 pairs and, across stages 2 and 3, pays
only one codimension-2 transition per aggregate. This is the optimistic
one-transition hypothesis. The exact arithmetic is checked in
[`PairDiagonalExcludedArithmetic.lean`](../OAI/Computability/FourierCircuit/PairDiagonalExcludedArithmetic.lean):

    W_pair       = 20,269,858,048
    W_pair_star  = 2^35 = 34,359,738,368
    P_optimistic = 2,261,309,952
    Delta_eff    = 163,863,040
    Delta_eff / (h^3 * W_pair_star)
                 = 320045 / 927712935936
                 = 3.4498279328e-7 (approximately)

Using the same logarithmic recurrence expression only as a numerical audit,
this corresponds to approximately 3.6183869234e-8. The Lean file proves the
integer values, positivity, and the normalized bound
`1e-9 < 320045/927712935936`; it deliberately does not prove the logarithmic
recurrence or the one-transition frame premise.

The ordinary current pair hierarchy charges four residual units per aggregate
(two directions and codimension two), giving a negative effective saving. The
one-transition number is therefore a concrete design target: it must be
realized by a cross-stage frame schedule, not assumed from the local rank
calculation.
