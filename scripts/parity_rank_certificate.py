#!/usr/bin/env python3
"""Constructive GF(2) rank certificate for the h=24 parity banks.

For S={0,1,2}, the zero bank contains indicators of triples disjoint from S
and the two bank contains indicators of triples meeting S in exactly two
coordinates.  This script does exact bit-vector arithmetic and checks both
the Gaussian-elimination ranks and explicit spanning witnesses:

* each outside basis vector e_i is a sum of three zero-bank indicators;
* the two-bank labels generate the 21 outside basis vectors and the two
  dimensional even subspace on S.

The result is an auditable finite computation, not a Lean theorem.  The Lean
file `ParityTargetAggregateFrameCandidate.lean` currently formalizes the
containment of both spans in the target orthogonal complement; this script
supplies the missing h=24 rank evidence without claiming a circuit schedule.
"""

from __future__ import annotations

from itertools import combinations

H = 24
TARGET = frozenset((0, 1, 2))
OUTSIDE = tuple(i for i in range(H) if i not in TARGET)
TRIPLES = tuple(combinations(range(H), 3))


def indicator(subset: frozenset[int] | tuple[int, ...]) -> int:
    value = 0
    for i in subset:
        value ^= 1 << i
    return value


def gf2_rank(rows: list[int]) -> int:
    """Rank of bit vectors over GF(2), by pivot elimination."""
    pivots: dict[int, int] = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    return len(pivots)


def xor(rows: list[int]) -> int:
    value = 0
    for row in rows:
        value ^= row
    return value


def zero_rows() -> list[int]:
    return [indicator(T) for T in TRIPLES if not (TARGET & frozenset(T))]


def two_rows() -> list[int]:
    return [indicator(T) for T in TRIPLES if len(TARGET & frozenset(T)) == 2]


def two_label(pair: frozenset[int], k: int) -> int:
    assert len(pair) == 2 and k not in pair
    return indicator(pair | {k})


def zero_witness(i: int) -> tuple[int, int, int, int]:
    """Return three zero-bank labels whose sum is e_i."""
    choices = [j for j in OUTSIDE if j != i]
    a, b, c = choices[:3]
    rows = [indicator((i, a, b)), indicator((i, a, c)), indicator((i, b, c))]
    witness = xor(rows)
    assert witness == indicator((i,))
    return a, b, c, witness


def two_witnesses() -> tuple[list[int], list[int]]:
    """Return 23 two-bank vectors spanning the target-perpendicular space.

    The first 21 vectors are e_k for k outside S.  The final two are
    e_1+e_2 and e_0+e_2.  All are explicit sums of two-bank labels.
    """
    k0 = OUTSIDE[0]
    p01 = frozenset((0, 1))
    p02 = frozenset((0, 2))
    p12 = frozenset((1, 2))
    even12 = xor([two_label(p01, k0), two_label(p02, k0)])
    even02 = xor([two_label(p01, k0), two_label(p12, k0)])
    assert even12 == indicator((1, 2))
    assert even02 == indicator((0, 2))

    # Their sum recovers p01, which removes the target part of any label.
    target_pair = even12 ^ even02
    assert target_pair == indicator((0, 1))
    outside_basis = [two_label(p01, k) ^ target_pair for k in OUTSIDE]
    assert outside_basis == [indicator((k,)) for k in OUTSIDE]
    return outside_basis, [even12, even02]


def audit() -> dict[str, object]:
    zrows = zero_rows()
    trows = two_rows()
    target = indicator(TARGET)
    assert len(zrows) == 1330
    assert len(trows) == 63

    # Every source row in both classes has even target intersection.
    assert all(bin(row & target).count("1") % 2 == 0 for row in zrows + trows)

    zero_basis = [indicator((i,)) for i in OUTSIDE]
    assert all(zero_witness(i)[-1] == e for i, e in zip(OUTSIDE, zero_basis))
    assert gf2_rank(zrows) == len(zero_basis) == 21

    outside_basis, target_even_basis = two_witnesses()
    two_basis = outside_basis + target_even_basis
    assert gf2_rank(two_basis) == 23
    assert gf2_rank(trows) == 23
    assert gf2_rank(zrows + trows) == 23

    # The target-perpendicular space is one nonzero linear equation in 24
    # coordinates, so its expected dimension is 23.  The explicit basis above
    # proves the two-bank span reaches that bound.
    return {
        "h": H,
        "target": tuple(sorted(TARGET)),
        "zero_support_count": len(zrows),
        "two_support_count": len(trows),
        "zero_rank_GF2": gf2_rank(zrows),
        "two_rank_GF2": gf2_rank(trows),
        "union_rank_GF2": gf2_rank(zrows + trows),
        "target_perp_expected_dimension": H - 1,
        "zero_witnesses": len(zero_basis),
        "two_witnesses": {"outside_basis": len(outside_basis),
                          "target_even_basis": len(target_even_basis)},
        "scope": (
            "exact finite GF(2) computation plus explicit spanning identities; "
            "not a Lean rank theorem or a physical circuit schedule"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
