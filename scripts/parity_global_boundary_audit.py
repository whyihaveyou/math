#!/usr/bin/env python3
"""Exact all-target audit for parity-split target boundaries.

For every target triple S on h=24 coordinates, the zero/two intersection
source indicators lie in S^perp over GF(2).  A tempting global shortcut would
place all these banks in one target-independent active frame.  This audit
checks the obstruction: the 2024 target indicators have GF(2) rank 24, so the
intersection of all S^perp is {0}.  The result is a linear-algebra no-go for a
common active frame; it is not a circuit lower bound and does not rule out
routing between target-labelled frames.
"""
from __future__ import annotations

from itertools import combinations
from math import comb

H = 24
TRIPLES = tuple(combinations(range(H), 3))
V = len(TRIPLES)


def bit_indicator(T: tuple[int, ...]) -> int:
    out = 0
    for i in T:
        out |= 1 << i
    return out


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


def audit() -> dict[str, object]:
    target_rows = [bit_indicator(S) for S in TRIPLES]
    rank = gf2_rank(target_rows)
    # For any fixed target, count all source classes by intersection size.
    S = TRIPLES[0]
    class_counts = {
        str(r): sum(len(set(S) & set(T)) == r for T in TRIPLES)
        for r in range(4)
    }
    expected = {"0": comb(H - 3, 3), "1": 3 * comb(H - 3, 2),
                "2": 3 * (H - 3), "3": 1}
    assert class_counts == expected
    # Double count target/source incidences in the two parity banks.
    all_target_zero_pairs = V * class_counts["0"]
    all_target_two_pairs = V * class_counts["2"]
    assert all_target_zero_pairs == V * comb(H - 3, 3)
    assert all_target_two_pairs == V * 3 * (H - 3)
    assert rank == H
    return {
        "h": H,
        "target_count": V,
        "target_indicator_rank_GF2": rank,
        "common_target_boundary_dimension": H - rank,
        "class_counts_for_each_target": class_counts,
        "all_target_zero_bank_incidence_pairs": all_target_zero_pairs,
        "all_target_two_bank_incidence_pairs": all_target_two_pairs,
        "all_target_parity_bank_pairs": all_target_zero_pairs + all_target_two_pairs,
        "conclusion": (
            "intersection of all target boundaries is zero; no nonzero "
            "target-independent active frame contains every parity bank"
        ),
        "scope": (
            "linear-algebra no-go only; target-labelled routing or extra address "
            "factors remain possible; no universal circuit lower bound"
        ),
    }


if __name__ == "__main__":
    import pprint
    pprint.pp(audit(), sort_dicts=False)
