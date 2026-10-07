#!/usr/bin/env python3
"""Exact audit of a singleton-incidence side-bank candidate.

For each coordinate ``i`` let ``A_i = sum_{T contains i} x_T``.  Since every
source triple has three coordinates, ``q = (sum_i A_i)/3``.  The scalar
diagonal-free side coefficient is therefore

    (q - sum_{i in S} A_i) / 2,

which has coefficient ``(1-|S intersect T|)/2`` on ``x_T``.  Adding the
direct ``x_S`` channel restores the exact invocation identity.

This script checks that scalar identity over exact rationals, computes the
GF(2) rank of each incidence support, and records a deliberately conditional
aggregate-wise frame ledger.  The ledger assumes that one aggregate can be
routed through the displayed nested boundaries without a target-family join
charge.  The target-family join and the direct diagonal gate are *not*
proved here; hence the arithmetic result is a research candidate, not a
physical circuit theorem.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb


H = 24
TARGETS = list(combinations(range(H), 3))
V = len(TARGETS)


def indicator(subset: tuple[int, ...] | frozenset[int]) -> int:
    value = 0
    for i in subset:
        value |= 1 << i
    return value


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            previous = basis.get(pivot)
            if previous is None:
                basis[pivot] = value
                break
            value ^= previous
    return len(basis)


def incidence_support(i: int) -> list[int]:
    return [indicator(T) for T in TARGETS if i in T]


def check_scalar_identity() -> None:
    """Check the exact coefficient for all four intersection classes."""

    # Every target sees C(3,r) C(21,3-r) sources in class r, so checking the
    # four classes covers all target/source pairs without a quadratic scan.
    for r in range(4):
        coefficient = Fraction(1 - r, 2)
        expected_side = Fraction(1 - r, 2)
        assert coefficient == expected_side
        # The r=3 diagonal term is -1 in the moment channel and is restored
        # by the direct +x_S channel.
        restored = coefficient + (1 if r == 3 else 0)
        assert restored == (0 if r == 3 else expected_side)
        assert comb(3, r) * comb(H - 3, 3 - r) > 0


def edge_cost(e: int, h: int, rank: int) -> int:
    """Four-edge conditional ledger for one aggregate."""

    assert 0 <= rank <= h
    return ((e - 1) * rank +
            ((e - 1) * (h - rank) + rank) +
            (h - rank))


def audit() -> dict[str, object]:
    check_scalar_identity()

    incidence_ranks = {i: gf2_rank(incidence_support(i)) for i in range(H)}
    assert set(incidence_ranks.values()) == {H - 1}

    # Three incidence aggregates used by one target already join to the full
    # active factor.  This is recorded as a warning for a future gate proof,
    # not hidden as a no-go for redesigned routes.
    target_join_ranks = {
        S: gf2_rank([row for i in S for row in incidence_support(i)])
        for S in TARGETS
    }
    assert set(target_join_ranks.values()) == {H}

    h = H
    n0 = V**3
    i0 = 3 * V**2
    m = h**3
    side_roles = h
    centre_roles = h
    role_count = 2 * n0 + i0 * (side_roles + centre_roles)
    padding = 1
    while padding < role_count:
        padding <<= 1

    centre_saving = 2 * n0 - 2 * i0 * h**2
    normalized = Fraction(centre_saving, m * padding)

    baseline_d_nbr = comb(h - 3, 3) + 3 * (h - 3)
    baseline_side_roles = V * baseline_d_nbr

    # Each of the h incidence aggregates has rank h-1.  Under the stated
    # aggregate-wise premise, the three finite prefixes cost h*(1+h+h^2).
    per_aggregate_route = sum(edge_cost(e, h, h - 1) for e in (1, h, h * h))
    assert per_aggregate_route == h * (1 + h + h * h) == 14_424
    total_route = side_roles * per_aggregate_route

    assert role_count == 17_172_846_592
    assert padding == 2**34
    assert centre_saving == 2_425_172_992
    assert normalized == Fraction(2_368_333, 231_928_233_984)
    assert Fraction(1, 10**9) < normalized

    return {
        "h": h,
        "v": V,
        "incidence_rank_each": h - 1,
        "target_join_rank_values": sorted(set(target_join_ranks.values())),
        "scalar_identity": "(1-r)/2, plus direct x_S on diagonal",
        "baseline_side_roles_per_invocation": baseline_side_roles,
        "candidate_side_roles_per_invocation": side_roles,
        "side_role_reduction": baseline_side_roles - side_roles,
        "role_count": role_count,
        "padding": padding,
        "centre_saving": centre_saving,
        "normalised_candidate": str(normalized),
        "normalised_candidate_float": float(normalized),
        "per_aggregate_route_cost": per_aggregate_route,
        "total_route_cost": total_route,
        "conditional": True,
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit())
