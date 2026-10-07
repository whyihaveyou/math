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

There is also a scalar obstruction to the simplest version of this proposal.
The three moments with `F subset S` see only triples meeting `S` in at least
two coordinates.  A triple `T` disjoint from `S` contributes zero to all three
of these moments, but the original side correction has coefficient `+1/2` on
such a `T` (over the characteristic-zero scalar model).  For example, at
`h >= 6`, take `S = {0,1,2}`, `T = {3,4,5}`, and a source vector supported on
`T`.  Any linear readout of the three diagonal-excluded pair moments is zero,
whereas the required correction is nonzero.  Thus the numerical pair-only
candidate below is **not even a complete scalar factorization**.  A viable
replacement must add the disjoint and one-intersection pair classes, or use a
different moment identity, before frame costs can be audited.

The scalar repair is explicit.  If `a_F = sum_{T superset F} x_T` and
`b_{F,S} = a_F - x_S` for `F subset S`, then the required diagonal-free side
coefficient can be written as

    side(S,x) = -(1/3) sum_{F subset S} b_{F,S}
                -(1/12) sum_{|F intersect S| = 1} a_F
                +(1/6) sum_{F intersect S = emptyset} a_F.

This identity is a scalar classification by intersection size, not a circuit
construction.  It says that all three pair classes suffice algebraically; it
also makes clear why the three `F subset S` moments alone do not.

The standalone Lean file
[`PairScalarNoGo.lean`](../OAI/Computability/FourierCircuit/PairScalarNoGo.lean)
also gives an eight-triple alternating witness at `h=6`: every ordered pair
moment and the global moment vanish, while the source is nonzero.  Hence those
aggregates cannot replace the entire source bank by any left inverse.  This
does not rule out a construction that retains a separate direct source term;
it records the information that pair/global moments alone lose.

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

The same scalar stress test was also instantiated at `h=34` in
[`PairDiagonalExcludedH34.lean`](../OAI/Computability/FourierCircuit/PairDiagonalExcludedH34.lean).
The exact values are

    v = 5984, pair_count = 561, W_pair = 492,470,944,768,
    W_pair_star = 2^39, Delta_eff = 140,010,280,960,
    Delta_eff / (h^3 W_pair_star) = 13915/2147483648.

The last fraction is approximately `6.4796768e-6`, and the same numerical
recurrence expression gives about `6.1250098e-7`.  The script accepts
`--h 34` and reproduces the rank facts and these integers.  This is a stronger
conditional arithmetic target, not evidence that the required one-transition
frame schedule or aggregate reuse exists.

The ordinary current pair hierarchy charges four residual units per aggregate
(two directions and codimension two), giving a negative effective saving. The
one-transition number is therefore a concrete design target: it must be
realized by a cross-stage frame schedule, not assumed from the local rank
calculation.

The companion script
[`pair_target_frame_intersection.py`](../scripts/pair_target_frame_intersection.py)
checks two separate reuse quantities.  For a fixed pair `F`, the
diagonal-excluded source span for each target `F union {k}` has rank `h-3`,
their **union** has rank `h-2`, and their intersection is zero (at both
`h=24` and `h=34`).  The zero intersection alone is not an obstruction: a
fixed accumulation frame must contain the union of the source spans.  If a
single fixed readout frame is also required to lie in every target label
`u_k^perp`, it is restricted to the two-dimensional intersection of those
target orthogonal complements.  The simultaneous inclusions would require
`H subset L subset H^perp` for the nondegenerate source span `H`, which is
impossible.  This is a conditional no-go for that fixed-frame, no-reframing
architecture, not a lower bound for arbitrary linear circuits; a real
improvement needs a target-dependent transport or a new shared encoding.

The Lean module
[`PairTargetFrameLocal.lean`](../OAI/Computability/FourierCircuit/PairTargetFrameLocal.lean)
formalizes the local statement without an enumeration-specific shortcut.  For
any pair-sized `F` and `k` outside `F`, the diagonal-excluded source labels are
linearly independent, span a submodule of the `k`-coordinate hyperplane, and
have exact dimension `h-3`.  It also proves that the common intersection of
these source spans over all `k` outside `F` is zero (for `h ≥ 4`).  These are
finite-field frame facts only; they make the reuse obligation explicit rather
than supplying the missing transport schedule.
