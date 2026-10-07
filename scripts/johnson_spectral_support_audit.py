#!/usr/bin/env python3
"""Exact Johnson-scheme spectral support audit for the h=24 side map.

Let V be the 3-subsets of [h], and let B_r[S,T]=1 when |S intersect T|=r.
The centre-compressed side correction has M=2A=B_0-B_2.  The Johnson
intersection algebra gives the exact annihilator

    (M-1267 I)(M+229 I)(M-2 I)=0.

This script computes the three rational spectral projectors in the B_r basis,
checks their ranks from trace, and counts support by intersection class.  It
is a conditional frame audit: every projector is dense in all four classes,
and the rank-2000 projector has a nonzero diagonal.  Thus a spectral/harmonic
factorization would need cancellation between terms on odd-intersection and
diagonal channels; it is not a sparse legal side bank under the published
pairwise-even source/target rule.  The audit does not rule out a new
non-spectral transport or a changed frame schedule.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb

H = 24
TRIPLES = tuple(combinations(range(H), 3))
V = len(TRIPLES)


def intersection_class(s: tuple[int, ...], t: tuple[int, ...]) -> int:
    return len(set(s).intersection(t))


def representatives() -> dict[int, tuple[tuple[int, ...], tuple[int, ...]]]:
    s = TRIPLES[0]
    return {
        r: (s, next(t for t in TRIPLES if intersection_class(s, t) == r))
        for r in range(4)
    }


def structure_constants() -> dict[tuple[int, int], tuple[int, ...]]:
    reps = representatives()
    table: dict[tuple[int, int], tuple[int, ...]] = {}
    for i in range(4):
        for j in range(4):
            values = []
            for r in range(4):
                s, u = reps[r]
                count = sum(
                    intersection_class(s, t) == i
                    and intersection_class(t, u) == j
                    for t in TRIPLES
                )
                values.append(count)
            table[i, j] = tuple(values)
    return table


def algebra_product(a: tuple[int, ...], b: tuple[int, ...], table):
    out = [0, 0, 0, 0]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            for r, coefficient in enumerate(table[i, j]):
                out[r] += ai * bj * coefficient
    return tuple(out)


def vec_add(*terms: tuple[Fraction, tuple[int, ...]]) -> tuple[Fraction, ...]:
    out = [Fraction(0) for _ in range(4)]
    for scale, vector in terms:
        for i, value in enumerate(vector):
            out[i] += scale * value
    return tuple(out)


def vec_scale(a: tuple[int, ...], q: Fraction) -> tuple[Fraction, ...]:
    return tuple(q * value for value in a)


def projector_polynomial(
    lam: int, other1: int, other2: int, m: tuple[int, ...], identity: tuple[int, ...], table
) -> tuple[Fraction, ...]:
    # (M-other1 I)(M-other2 I) / ((lam-other1)(lam-other2)).
    m2 = algebra_product(m, m, table)
    numerator = vec_add(
        (Fraction(1), m2),
        (Fraction(-(other1 + other2)), m),
        (Fraction(other1 * other2), identity),
    )
    denominator = Fraction((lam - other1) * (lam - other2))
    return tuple(value / denominator for value in numerator)


def support_counts(coefficients: tuple[Fraction, ...]) -> dict[str, object]:
    class_counts = {r: comb(3, r) * comb(H - 3, 3 - r) for r in range(4)}
    nonzero_classes = [r for r, value in enumerate(coefficients) if value != 0]
    return {
        "coefficients_B0_B1_B2_B3": [str(value) for value in coefficients],
        "nonzero_intersection_classes": nonzero_classes,
        "nonzero_entries_per_row": sum(class_counts[r] for r in nonzero_classes),
        "support_entries_total": V * sum(class_counts[r] for r in nonzero_classes),
        "diagonal_coefficient": str(coefficients[3]),
        "diagonal_entries": V if coefficients[3] else 0,
        "class_cardinalities": class_counts,
    }


def audit() -> dict[str, object]:
    table = structure_constants()
    m = (1, 0, -1, 0)  # B_0 - B_2
    identity = (0, 0, 0, 1)  # B_3
    m2 = algebra_product(m, m, table)
    m3 = algebra_product(m2, m, table)
    annihilator = tuple(
        m3[r] - 1040 * m2[r] - 288067 * m[r] + 580286 * identity[r]
        for r in range(4)
    )
    assert annihilator == (0, 0, 0, 0)

    eigenvalues = (1267, -229, 2)
    projectors = {
        "P_1267": projector_polynomial(1267, -229, 2, m, identity, table),
        "P_neg229": projector_polynomial(-229, 1267, 2, m, identity, table),
        "P_2": projector_polynomial(2, 1267, -229, m, identity, table),
    }
    # Projectors sum to identity and are mutually orthogonal in the algebra.
    sum_projectors = vec_add(*[(Fraction(1), value) for value in projectors.values()])
    assert sum_projectors == tuple(Fraction(x) for x in identity)
    for name, p in projectors.items():
        p2 = algebra_product(tuple(int(x) for x in p), tuple(int(x) for x in p), table) if all(x.denominator == 1 for x in p) else None
        # Avoid integer-only helper: direct rational multiplication in the basis.
        pp = [Fraction(0) for _ in range(4)]
        for i, ai in enumerate(p):
            for j, bj in enumerate(p):
                for r, c in enumerate(table[i, j]):
                    pp[r] += ai * bj * c
        assert tuple(pp) == p, (name, pp, p)

    # The diagonal coefficient times V is the trace, hence the rank for these
    # idempotent symmetric Johnson projectors.
    ranks = {name: projectors[name][3] * V for name in projectors}
    assert ranks == {"P_1267": 1, "P_neg229": 23, "P_2": 2000}
    supports = {name: support_counts(p) for name, p in projectors.items()}
    assert all(s["nonzero_intersection_classes"] == [0, 1, 2, 3] for s in supports.values())
    assert all(s["diagonal_entries"] == V for s in supports.values())

    # Weighted diagonal cancellation recovers M's zero diagonal.  This is the
    # exact cancellation that a pairwise-even frame schedule would have to
    # realize if it uses the spectral projectors.
    diagonal = (
        Fraction(1267) * projectors["P_1267"][3]
        + Fraction(-229) * projectors["P_neg229"][3]
        + Fraction(2) * projectors["P_2"][3]
    )
    assert diagonal == 0

    return {
        "h": H,
        "triple_count_v": V,
        "M": "B0 - B2",
        "M_squared_B0_to_B3": list(m2),
        "annihilator": "(z-1267)(z+229)(z-2)",
        "annihilator_B0_to_B3": list(annihilator),
        "eigenvalues": list(eigenvalues),
        "projector_ranks": ranks,
        "projectors": supports,
        "weighted_projector_diagonal_sum": str(diagonal),
        "conditional_conclusion": (
            "all three spectral projectors are dense in intersection classes 0,1,2,3; "
            "each has 2024 nonzero diagonal entries; legal pairwise-even support "
            "therefore requires cancellation or a redesigned frame transport"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
