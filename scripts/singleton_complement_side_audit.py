#!/usr/bin/env python3
"""Exact audit of a singleton-complement side grouping.

For a target triple S, let C=S^c.  Instead of the pair groups used by the
pair/complement candidate, group the r=0 sources by one outside singleton:

    D_i(S) = sum_{T: i in T, T intersect S = empty} x_T   (i in C),
    E_2(S) = sum_{T: |T intersect S| = 2} x_T.

Every r=0 triple is counted three times by the D_i, while E_2 counts each
r=2 triple once.  Thus the exact even side correction is

    side(S,x) = (1/6) sum_{i in C} D_i(S) - (1/2) E_2(S).

All aggregates have source labels in t_S^perp.  The construction is a
useful source-support-compatible scalar candidate, but it uses 22 target-indexed side
roles (rather than 2 for the parity split or 213 for pair groups).  At h=24
it remains in the 2^40 width bucket.  The rank audit records the conditional
full-active-to-family-support-to-full penalty: the join of all D_i supports
has rank h-3 and E_2 has rank h-1, so the optimistic joint family codimension
is 3+1=4.  This already overwhelms the centre saving.  The charge is a
conditional obstruction for the existing full-frame boundary; it is not a
lower bound for a sequential or redesigned schedule.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb

H = 24
TARGET = frozenset((0, 1, 2))
TRIPLES = tuple(combinations(range(H), 3))
V = len(TRIPLES)


def indicator(subset: frozenset[int] | tuple[int, ...]) -> int:
    value = 0
    for coordinate in subset:
        value |= 1 << coordinate
    return value


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def intersection_class(source: tuple[int, ...]) -> int:
    return len(frozenset(source) & TARGET)


def d_support(i: int) -> list[int]:
    return [
        indicator(source)
        for source in TRIPLES
        if i in source and not (frozenset(source) & TARGET)
    ]


def e2_support() -> list[int]:
    return [indicator(source) for source in TRIPLES if intersection_class(source) == 2]


def scalar_identity() -> None:
    outside = sorted(set(range(H)) - TARGET)
    for source in TRIPLES:
        r = intersection_class(source)
        d_mult = sum(source_i in source for source_i in outside) if r == 0 else 0
        # D_i contributes 1/6 for each outside member; E2 contributes -1/2.
        coefficient = Fraction(d_mult, 6) - (Fraction(1, 2) if r == 2 else 0)
        expected = Fraction(1, 2) if r == 0 else -Fraction(1, 2) if r == 2 else Fraction(0)
        assert coefficient == expected, (source, r, coefficient, expected)


def audit() -> dict[str, object]:
    scalar_identity()
    outside = sorted(set(range(H)) - TARGET)
    d_rows = {i: d_support(i) for i in outside}
    e_rows = e2_support()
    d_join = [row for rows in d_rows.values() for row in rows]
    ranks = {
        "D_i_each": {str(i): gf2_rank(rows) for i, rows in d_rows.items()},
        "D_i_join": gf2_rank(d_join),
        "E2": gf2_rank(e_rows),
        "D_join_plus_E2": gf2_rank(d_join + e_rows),
    }
    expected_each = {str(i): H - 4 for i in outside}
    assert ranks["D_i_each"] == expected_each
    assert ranks["D_i_join"] == H - 3
    assert ranks["E2"] == H - 1
    assert ranks["D_join_plus_E2"] == H - 1
    target_vector = indicator(TARGET)
    assert all(bin(row & target_vector).count("1") % 2 == 0 for row in d_join + e_rows)

    class_counts = {
        "r0": sum(intersection_class(source) == 0 for source in TRIPLES),
        "r2": sum(intersection_class(source) == 2 for source in TRIPLES),
    }
    assert class_counts == {"r0": comb(H - 3, 3), "r2": 3 * (H - 3)}

    n0 = V**3
    i0 = 3 * V**2
    m = H**3
    side_roles = (H - 3) + 1
    centre_roles = H
    role_count = 2 * n0 + i0 * (side_roles * V + centre_roles)
    padding = 1
    while padding < role_count:
        padding <<= 1
    centre_saving = 2 * n0 - 2 * i0 * H**2
    nominal_margin = centre_saving

    # The D_i family joins to rank h-3 (codim 3); E2 has rank h-1
    # (codim 1).  This is the optimistic *joint-family* charge; treating
    # each D_i separately is strictly more expensive.
    codim_join = (H - ranks["D_i_join"]) + (H - ranks["E2"])
    one_way_penalty = i0 * V * codim_join
    round_trip_penalty = 2 * one_way_penalty

    return {
        "h": H,
        "target": tuple(sorted(TARGET)),
        "v": V,
        "class_counts": class_counts,
        "D_i_count": len(outside),
        "D_i_support_size": len(next(iter(d_rows.values()))),
        "E2_support_size": len(e_rows),
        "support_ranks_GF2": ranks,
        "all_supports_inside_target_perp": True,
        "N0": n0,
        "I0": i0,
        "side_roles_per_target": side_roles,
        "side_roles_per_invocation": side_roles * V,
        "centre_roles_per_invocation": centre_roles,
        "role_count": role_count,
        "padding": padding,
        "centre_saving": centre_saving,
        "nominal_normalized_margin": str(Fraction(nominal_margin, m * padding)),
        "joint_family_codimension": codim_join,
        "one_direction_penalty": one_way_penalty,
        "round_trip_penalty": round_trip_penalty,
        "effective_margin_round_trip": centre_saving - round_trip_penalty,
        "effective_normalized_margin_round_trip": str(
            Fraction(centre_saving - round_trip_penalty, m * padding)
        ),
        "conditional_scope": (
            "joint D_i-family/E2 full-active-to-support-to-full charge under the "
            "existing boundary; not a universal lower bound"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
