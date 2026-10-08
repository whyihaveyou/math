#!/usr/bin/env python3
"""Exact audit after eliminating the redundant global side moment.

For every source triple T, exactly three incidence coordinates contain T, so
the global moment q=sum_T x_T satisfies sum_i a_i=3q.  Over characteristic
zero this lets the side readout use only the 24 incidence moments.  The
resulting h=24 width drops just below 2^34.  The script also reports the
existing direct-diagonal frame charge, which remains an open physical
obligation and is negative under that ledger.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb


H = 24
TRIPLES = list(combinations(range(H), 3))


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                basis[pivot] = value
                break
            value ^= old
    return len(basis)


def incidence_row(i: int) -> int:
    value = 0
    for column, triple in enumerate(TRIPLES):
        if i in triple:
            value |= 1 << column
    return value


def audit() -> dict[str, object]:
    rows = [incidence_row(i) for i in range(H)]
    # The 24 incidence moments are linearly independent over F_2 at h=24;
    # the all-ones source functional is (1/3) times their sum over Q.
    assert gf2_rank(rows) == H
    assert all(sum(i in t for t in TRIPLES) == comb(H - 1, 2) for i in range(H))
    assert all(sum(i in t for i in t) == 3 for t in TRIPLES)

    v = len(TRIPLES)
    n0 = v**3
    i0 = 3 * v**2
    m = H**3
    side_roles = H
    centre_roles = H
    width = 2 * n0 + i0 * (side_roles + centre_roles)
    padding = 1
    while padding < width:
        padding <<= 1
    previous_padding = 2**35
    centre_saving = 2 * n0 - 2 * i0 * H**2
    normalized = Fraction(centre_saving, m * padding)

    # Existing eight-row direct-diagonal ledger.  This remains conditional;
    # it is shown to make the remaining physical gap explicit.
    direct_penalty = 2 * i0 * v
    direct_margin = centre_saving - direct_penalty
    direct_normalized = Fraction(direct_margin, m * padding)

    assert width == 17172846592
    assert padding == 2**34
    assert width <= padding < previous_padding
    assert centre_saving == 2425172992
    assert normalized == Fraction(2368333, 231928233984)
    assert normalized > Fraction(1, 10**9)
    assert direct_margin == -47323645952
    assert direct_normalized == Fraction(-23107249, 115964116992)

    return {
        "h": H,
        "triple_count": v,
        "incidence_rank_GF2": gf2_rank(rows),
        "incidence_sum_per_source": 3,
        "width_without_global_moment": width,
        "padding": padding,
        "previous_padding": previous_padding,
        "padding_crossing": True,
        "centre_saving": centre_saving,
        "normalized_margin": str(normalized),
        "normalized_margin_float": float(normalized),
        "direct_diagonal_penalty_existing_ledger": direct_penalty,
        "direct_diagonal_margin": direct_margin,
        "direct_diagonal_normalized": str(direct_normalized),
        "interpretation": (
            "exact scalar redundancy and conditional width improvement; direct "
            "diagonal gate/frame route remains unproved"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
