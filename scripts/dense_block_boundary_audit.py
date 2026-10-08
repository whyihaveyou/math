#!/usr/bin/env python3
"""Exact h=24 audit for the two-frame dense-complement cover.

Let u=e_0 and w=1+e_0. Targets containing 0 are routed to w; targets
avoiding 0 are routed to u. This checks:

* the common intersection of target boundaries in each block is exactly the
  routed one-dimensional line;
* every individual target boundary has dimension 23;
* target-indexed parity matrices retain large rank inside each block.

All ranks are exact Gaussian elimination over F_2. These are label/span and
linear-factorization facts, not complex-gate, global-schedule, or all-length
DFT claims.
"""

from __future__ import annotations

from itertools import combinations
from math import comb
from fractions import Fraction

H = 24
ZERO = 0
TRIPLES = tuple(combinations(range(H), 3))
TARGET_BITS = tuple(sum(1 << i for i in t) for t in TRIPLES)
TARGET_COUNT = len(TRIPLES)


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                basis[pivot] = value
                break
            value ^= old
    return len(basis)


def dot_parity(left: int, right: int) -> int:
    return bin(left & right).count("1") & 1


def indicator_matrix_rows(target_indices: list[int], kind: str) -> list[int]:
    """Rows of target-vs-source parity matrix as packed source columns."""
    if kind not in {"zero", "two", "even"}:
        raise ValueError(kind)
    rows: list[int] = []
    for target_index in target_indices:
        target = TARGET_BITS[target_index]
        row = 0
        for source_index, source in enumerate(TARGET_BITS):
            overlap = bin(target & source).count("1")
            if kind == "zero":
                ok = overlap == 0
            elif kind == "two":
                ok = overlap == 2
            else:
                ok = overlap % 2 == 0
            if ok:
                row |= 1 << source_index
        rows.append(row)
    return rows


def block_boundary_rank(target_indices: list[int]) -> int:
    return gf2_rank([TARGET_BITS[i] for i in target_indices])


def verify_common_line(target_indices: list[int], expected: int) -> None:
    assert expected != 0
    assert all(dot_parity(TARGET_BITS[i], expected) == 0 for i in target_indices)
    assert H - block_boundary_rank(target_indices) == 1


def audit() -> dict[str, object]:
    contains_zero = [i for i, t in enumerate(TRIPLES) if ZERO in t]
    avoids_zero = [i for i, t in enumerate(TRIPLES) if ZERO not in t]
    assert len(contains_zero) == comb(H - 1, 2) == 253
    assert len(avoids_zero) == comb(H - 1, 3) == 1771
    assert len(contains_zero) + len(avoids_zero) == TARGET_COUNT == 2024

    unit = 1 << ZERO
    dense = ((1 << H) - 1) ^ unit
    eligible = [
        tuple(j for j, label in enumerate((unit, dense)) if dot_parity(target, label) == 0)
        for target in TARGET_BITS
    ]
    assert all(len(frames) == 1 for frames in eligible)
    assert dot_parity(unit, dense) == 0
    assert bin(unit).count("1") == 1 and bin(dense).count("1") == H - 1
    assert dot_parity(unit, unit) == dot_parity(dense, dense) == 1

    rank_contains = block_boundary_rank(contains_zero)
    rank_avoids = block_boundary_rank(avoids_zero)
    verify_common_line(contains_zero, dense)
    verify_common_line(avoids_zero, unit)
    assert rank_contains == rank_avoids == H - 1
    assert all(block_boundary_rank([i]) == 1 for i in range(TARGET_COUNT))

    matrix_ranks: dict[str, dict[str, int]] = {}
    for block_name, indices in (("contains_zero", contains_zero), ("avoids_zero", avoids_zero)):
        matrix_ranks[block_name] = {
            kind: gf2_rank(indicator_matrix_rows(indices, kind))
            for kind in ("zero", "two", "even")
        }
    # Keep exact ranks; a block may have linear dependencies in a parity class.

    prefix_sum = 1 + H + H * H
    switch_only_charge = 2 * prefix_sum
    centre_saving = 2_425_172_992
    base_padding = 2**45
    margin = centre_saving - switch_only_charge
    normalized = Fraction(margin, H**3 * base_padding)
    assert normalized == Fraction(1212585895, 243194379878006784)
    assert switch_only_charge == 1202
    assert margin == 2_425_171_790

    return {
        "h": H,
        "target_count": TARGET_COUNT,
        "contains_zero_targets": len(contains_zero),
        "avoids_zero_targets": len(avoids_zero),
        "dense_labels": {"u": unit, "w": dense},
        "eligible_frames_per_target": {1: TARGET_COUNT},
        "target_boundary_rank": H - 1,
        "contains_zero_constraint_rank": rank_contains,
        "avoids_zero_constraint_rank": rank_avoids,
        "contains_zero_common_boundary_dimension": H - rank_contains,
        "avoids_zero_common_boundary_dimension": H - rank_avoids,
        "contains_zero_common_line": "w = allOnes + e0",
        "avoids_zero_common_line": "u = e0",
        "parity_matrix_GF2_ranks": matrix_ranks,
        "switch_only_charge_conditional": switch_only_charge,
        "centre_saving": centre_saving,
        "conditional_margin": margin,
        "conditional_normalized_margin_exact": str(normalized),
        "conditional_normalized_margin": float(normalized),
        "scope": (
            "exact binary block-boundary and target-indexed linear-rank audit; "
            "no complex gate, global schedule, or all-length DFT theorem"
        ),
    }


if __name__ == "__main__":
    import pprint
    pprint.pp(audit(), sort_dicts=False)
