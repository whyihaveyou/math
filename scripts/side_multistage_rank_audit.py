#!/usr/bin/env python3
"""Exact rank certificate for multi-stage linear side-wire redesigns.

For h=24 and triples S,T, the centre-compressed side correction has matrix

    A[S,T] = +1/2  (|S ∩ T| = 0),
             -1/2  (|S ∩ T| = 2),
              0    otherwise (including S=T).

Write M = 2 A = B_0 - B_2, where B_k is the Johnson-scheme matrix whose
(S,T) entry is one when |S∩T|=k.  The script computes the exact intersection
class multiplication table and verifies

    (M - 1267 I) (M + 229 I) (M - 2 I) = 0.

The constant term of this polynomial is 580286 != 0, so M (and A) is
invertible.  Consequently any *linear* multi-stage factorisation of the side
map through banks of dimensions r_1,...,r_q has

    v = rank(A) <= sum_i r_i,   v = C(24,3) = 2024.

This rules out a reduction in total side-bank coordinates for arbitrary
linear copies, even if several banks are used at different stages.  It does
not rule out nonlinear circuits, a change in the cost model, or a schedule
whose side coordinates are not an auxiliary linear factorisation.
"""

from __future__ import annotations

from itertools import combinations
from typing import Iterable

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
    """Return p[i,j,r] for B_i B_j = sum_r p[i,j,r] B_r."""
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
                values.append(int(count))
            table[i, j] = tuple(values)
    return table


def algebra_product(
    a: Iterable[int], b: Iterable[int], table: dict[tuple[int, int], tuple[int, ...]]
) -> tuple[int, ...]:
    out = [0, 0, 0, 0]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            for r, coefficient in enumerate(table[i, j]):
                out[r] += ai * bj * coefficient
    return tuple(out)


def audit() -> dict[str, object]:
    table = structure_constants()
    m = (1, 0, -1, 0)  # B_0 - B_2
    identity = (0, 0, 0, 1)  # B_3
    m2 = algebra_product(m, m, table)
    m3 = algebra_product(m2, m, table)

    # (z - 1267)(z + 229)(z - 2) = z^3 - 1040 z^2 - 288067 z + 580286.
    polynomial = (1, -1040, -288067, 580286)
    annihilator = tuple(
        m3[r] + polynomial[1] * m2[r] + polynomial[2] * m[r]
        + polynomial[3] * identity[r]
        for r in range(4)
    )
    assert annihilator == (0, 0, 0, 0)
    constant = polynomial[3]
    assert constant != 0

    # A factorisation through q banks with dimensions r_i is a map
    # A = sum_i J_i V_i; rank(A) <= sum_i r_i.  Since M=2A is invertible,
    # rank(A)=V, giving the exact lower bound below.
    return {
        "h": H,
        "triple_count_v": V,
        "matrix": "M = B_0 - B_2 = 2*A",
        "structure_constants_BiBj": {
            f"B{i}*B{j}": list(table[i, j])
            for i in range(4)
            for j in range(4)
        },
        "M_squared_coefficients_B0_to_B3": list(m2),
        "M_cubed_coefficients_B0_to_B3": list(m3),
        "annihilating_polynomial": "z^3 - 1040 z^2 - 288067 z + 580286",
        "annihilator_coefficients_B0_to_B3": list(annihilator),
        "nonzero_constant_term": constant,
        "rank_M_over_Q": V,
        "rank_A_over_Q": V,
        "linear_multistage_total_bank_dimension_lower_bound": V,
        "strict_scope": (
            "linear additive source/auxiliary maps; excludes nonlinear circuits "
            "and cost models that do not charge auxiliary coordinates"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
