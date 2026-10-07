#!/usr/bin/env python3
"""Global parity-bank and shared-boundary audit.

The local parity certificate is target indexed: for a fixed target ``S``,
source triples with ``|S ∩ T|`` equal to zero or two have indicator labels in
the target boundary ``t_S^⊥``.  This script checks whether the same source
bank can serve *all* targets while staying in one target-independent frame.

There are two separate exact tests:

* The union of the zero (or of the two) classes over all targets contains
  every triple indicator.  At ``h=24`` those indicators span all of
  ``F_2^h``.  Thus a common bank which literally contains every local source
  label cannot lie in any codimension-one target boundary.
* The target-by-source incidence matrix for the two-intersection aggregate
  has full rank over ``F_2`` (2024 at ``h=24``).  Consequently it also has
  full rank over characteristic-zero fields: an odd determinant survives over
  ``Q`` and hence over ``C``.  Under the explicit linear-bank factorization
  premise ``A_2 = R B`` this forces at least 2024 common bank channels.

These are conditional no-go statements.  They do not rule out a nonlinear
or interactive source formation, a target-dependent frame change, or a new
factorization that does not expose the parity aggregate as a linear bank.
"""

from __future__ import annotations

import argparse
from itertools import combinations
from typing import Iterable


def indicator(subset: Iterable[int]) -> int:
    value = 0
    for i in subset:
        value |= 1 << i
    return value


def gf2_rank(rows: Iterable[int]) -> int:
    """Exact rank of bit-vector rows over GF(2)."""
    pivots: dict[int, int] = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            old = pivots.get(pivot)
            if old is None:
                pivots[pivot] = value
                break
            value ^= old
    return len(pivots)


def class_rows(h: int, intersection: int) -> list[int]:
    """Rows of the target-by-source class-incidence matrix over GF(2).

    A row is indexed by a target triple S and a bit is set at source triple T
    exactly when ``|S ∩ T| == intersection``.
    """
    triples = tuple(combinations(range(h), 3))
    rows: list[int] = []
    for source_target in triples:
        S = set(source_target)
        row = 0
        for j, T in enumerate(triples):
            if len(S.intersection(T)) == intersection:
                row |= 1 << j
        rows.append(row)
    return rows


def source_labels_for_class(h: int, intersection: int) -> set[int]:
    """Union of source indicator labels over every target triple."""
    triples = tuple(combinations(range(h), 3))
    labels: set[int] = set()
    for S_tuple in triples:
        S = set(S_tuple)
        for T in triples:
            if len(S.intersection(T)) == intersection:
                labels.add(indicator(T))
    return labels


def local_rank(h: int, target: tuple[int, int, int], intersection: int) -> int:
    rows = []
    target_set = set(target)
    for T in combinations(range(h), 3):
        if len(target_set.intersection(T)) == intersection:
            rows.append(indicator(T))
    return gf2_rank(rows)


def first_boundary_witness(
    h: int, target: tuple[int, int, int], labels: set[int], *, exclude_target: bool = False
):
    """Return a label with odd target dot product, if one exists."""
    target_mask = indicator(target)
    for label in sorted(labels):
        if exclude_target and label == target_mask:
            continue
        if bin(label & target_mask).count("1") % 2:
            return tuple(i for i in range(h) if (label >> i) & 1)
    return None


def audit(h: int = 24) -> dict[str, object]:
    if h < 6:
        raise ValueError("h >= 6 is required for the disjoint witness argument")
    triples = tuple(combinations(range(h), 3))
    v = len(triples)
    target = triples[0]

    zero_labels = source_labels_for_class(h, 0)
    two_labels = source_labels_for_class(h, 2)
    zero_rows = class_rows(h, 0)
    two_rows = class_rows(h, 2)
    even_rows = [a ^ b for a, b in zip(zero_rows, two_rows)]

    # Each union already contains every triple indicator.  The direct set
    # check is retained so the conclusion does not depend only on a rank.
    all_labels = {indicator(T) for T in triples}
    assert zero_labels == all_labels
    assert two_labels == all_labels
    global_zero_rank = gf2_rank(zero_labels)
    global_two_rank = gf2_rank(two_labels)

    # The fixed-target boundary has codimension one.  The global bank has
    # full rank and therefore violates it for every target; record witnesses.
    witnesses = {
        S: first_boundary_witness(h, S, zero_labels, exclude_target=True) for S in triples
    }
    witnesses_two = {
        S: first_boundary_witness(h, S, two_labels, exclude_target=True) for S in triples
    }
    assert all(witnesses.values())
    assert all(witnesses_two.values())

    # Matrix ranks: rows are target aggregates, columns are source triples.
    # A full GF(2) rank of A2 gives a full rank certificate over Q/C because
    # the square determinant is odd.
    rank_a0 = gf2_rank(zero_rows)
    rank_a2 = gf2_rank(two_rows)
    rank_aeven = gf2_rank(even_rows)

    return {
        "h": h,
        "target_count_v": v,
        "local_fixed_target": {
            "target": target,
            "zero_rank": local_rank(h, target, 0),
            "two_rank": local_rank(h, target, 2),
            "target_boundary_dimension": h - 1,
        },
        "global_source_label_unions": {
            "zero_unique_labels": len(zero_labels),
            "two_unique_labels": len(two_labels),
            "all_triple_labels": len(all_labels),
            "zero_union_rank_GF2": global_zero_rank,
            "two_union_rank_GF2": global_two_rank,
            "global_active_dimension": h,
            "zero_union_is_all_triples": zero_labels == all_labels,
            "two_union_is_all_triples": two_labels == all_labels,
        },
        "common_boundary_test": {
            "targets_with_zero_bank_odd_witness": sum(bool(x) for x in witnesses.values()),
            "targets_with_two_bank_odd_witness": sum(bool(x) for x in witnesses_two.values()),
            "target_count": v,
            "example_target": target,
            "zero_example_odd_label": witnesses[target],
            "two_example_odd_label": witnesses_two[target],
            "conclusion": (
                "under the literal-common-label premise, neither global bank "
                "is contained in any fixed target boundary"
            ),
        },
        "target_by_source_incidence_ranks_GF2": {
            "A_zero": rank_a0,
            "A_two": rank_a2,
            "A_even_zero_or_two": rank_aeven,
        },
        "linear_bank_factorization": {
            "A_two_rank_over_Q_or_C_at_least": rank_a2,
            "minimum_common_channels_under_A_two_equals_RB": rank_a2,
            "reason": (
                "A_two is a square integer matrix and its full GF(2) rank "
                "certifies an odd nonzero determinant"
            ),
        },
        "scope": (
            "conditional on literal common source labels or a linear bank/readout "
            "factorization; no universal lower bound for nonlinear, interactive, "
            "or target-dependent routing"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--h", type=int, default=24)
    args = parser.parse_args()
    import pprint

    pprint.pp(audit(args.h), sort_dicts=False)


if __name__ == "__main__":
    main()
