#!/usr/bin/env python3
"""Exact audit of a parity-split target aggregate.

For a target triple S split the off-diagonal side correction into

  a0(S) = sum_{|S∩T|=0} x_T,
  a2(S) = sum_{|S∩T|=2} x_T,

with readout +(1/2)a0-(1/2)a2.  This is a scalar identity distinct from the
single all-even target aggregate.  The script checks the coefficient identity,
computes exact GF(2) source-label ranks of the two support families, and
records a conditional frame charge if each aggregate must leave the full
active factor and return to its target subspace.

The conditional charge is deliberately explicit: the r=0 support has rank
h-3, so its full-to-support-to-full excursion costs 2*3 directions; the r=2
support has rank h-1 and costs 2 directions.  This is not a universal lower
bound for redesigned stages or sequential target routing.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb

H = 24
TARGET = frozenset((0, 1, 2))
TRIPLES = tuple(combinations(range(H), 3))
V = len(TRIPLES)


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def indicator(subset: frozenset[int] | tuple[int, ...]) -> int:
    value = 0
    for coordinate in subset:
        value |= 1 << coordinate
    return value


def intersection_class(source: tuple[int, ...]) -> int:
    return len(frozenset(source) & TARGET)


def coefficient_identity() -> dict[int, Fraction]:
    coefficients: dict[int, Fraction] = {}
    for source in TRIPLES:
        r = intersection_class(source)
        reconstructed = Fraction(1, 2) if r == 0 else (
            -Fraction(1, 2) if r == 2 else Fraction(0)
        )
        expected = reconstructed if source != tuple(sorted(TARGET)) else Fraction(0)
        # The r=3 source is the target and is excluded from both aggregates.
        coefficients.setdefault(r, reconstructed)
        assert reconstructed == expected, (source, r, reconstructed, expected)
    return coefficients


def class_support(intersection: int) -> list[int]:
    return [indicator(source) for source in TRIPLES if intersection_class(source) == intersection]


def audit() -> dict[str, object]:
    classes = {r: class_support(r) for r in (0, 2)}
    ranks = {f"r{r}": gf2_rank(rows) for r, rows in classes.items()}
    target_vector = indicator(TARGET)
    assert ranks == {"r0": H - 3, "r2": H - 1}
    assert all(
        sum(((target_vector >> bit) & 1) * ((row >> bit) & 1) for bit in range(H)) % 2 == 0
        for rows in classes.values()
        for row in rows
    )
    joined_rank = gf2_rank(classes[0] + classes[2])
    assert joined_rank == H - 1

    # Check all four intersection classes in the scalar side coefficient.
    scalar_counts = {r: sum(intersection_class(source) == r for source in TRIPLES) for r in range(4)}
    scalar_coefficients = coefficient_identity()

    n0 = V**3
    i0 = 3 * V**2
    m = H**3
    side_roles = 2 * V
    centre_roles = H
    role_count = 2 * n0 + i0 * (side_roles + centre_roles)
    padding = 1
    while padding < role_count:
        padding <<= 1
    centre_saving = 2 * n0 - 2 * i0 * H**2

    # Full-to-support-to-full cost: 2*(H-rank) per target aggregate.
    codim_r0 = H - ranks["r0"]
    codim_r2 = H - ranks["r2"]
    one_direction_penalty = i0 * V * (codim_r0 + codim_r2)
    round_trip_penalty = 2 * one_direction_penalty
    effective_margin = centre_saving - round_trip_penalty

    return {
        "h": H,
        "target": tuple(sorted(TARGET)),
        "v": V,
        "class_counts": scalar_counts,
        "scalar_side_coefficients_by_intersection": {
            str(r): str(value) for r, value in sorted(scalar_coefficients.items())
        },
        "support_counts": {f"r{r}": len(rows) for r, rows in classes.items()},
        "support_ranks_GF2": ranks,
        "target_hyperplane_join_rank": joined_rank,
        "supports_inside_target_perp": True,
        "N0": n0,
        "I0": i0,
        "side_roles_per_invocation": side_roles,
        "centre_roles_per_invocation": centre_roles,
        "role_count": role_count,
        "padding": padding,
        "centre_saving": centre_saving,
        "codimension_r0": codim_r0,
        "codimension_r2": codim_r2,
        "one_direction_penalty": one_direction_penalty,
        "round_trip_penalty": round_trip_penalty,
        "effective_margin_round_trip": effective_margin,
        "effective_normalized_margin_round_trip": str(Fraction(effective_margin, m * padding)),
        "conditional_scope": (
            "full-active-to-each-class-support and return, with one aggregate per target; "
            "not a universal lower bound for sequential routing or redesigned boundaries"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
