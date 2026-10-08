#!/usr/bin/env python3
"""Exact h=24 audit for diagonal-excluded pair/complement side wires.

For a fixed target ``S`` and pair ``F`` used by the pair/complement readout,
remove the diagonal source ``T=S`` from the aggregate support.  The ``A``
bank (``F subset S``) then has 21 independent labels, whereas the ``B`` bank
(``F`` disjoint from ``S``) still has rank 22: deleting one disjoint triple
does not lower its span.  The joins of the target-local families have ranks
23 and 24 respectively.  These are exact GF(2) computations on the finite
h=24 label set.

The script also evaluates the existing pair/complement width and the
aggregate-wise conditional boundary ledger.  It deliberately does not call
the rank calculation a circuit schedule: a complex implementation, scalar
commutation, and a global all-prefix DAG remain open.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


H = 24
TARGET = (0, 1, 2)
TRIPLES = list(combinations(range(H), 3))
PAIRS = list(combinations(range(H), 2))


def indicator(subset: tuple[int, ...] | frozenset[int]) -> int:
    result = 0
    for coordinate in subset:
        result |= 1 << coordinate
    return result


TRIPLE_MASKS = {triple: indicator(triple) for triple in TRIPLES}


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


def a_rows(pair: tuple[int, int], target: tuple[int, int, int]) -> list[int]:
    pair_set = set(pair)
    return [
        TRIPLE_MASKS[triple]
        for triple in TRIPLES
        if pair_set.issubset(triple) and triple != target
    ]


def b_rows(pair: tuple[int, int], target: tuple[int, int, int]) -> list[int]:
    pair_set = set(pair)
    return [
        TRIPLE_MASKS[triple]
        for triple in TRIPLES
        if pair_set.isdisjoint(triple) and triple != target
    ]


def audit() -> dict[str, object]:
    target_set = set(TARGET)
    a_pairs = [pair for pair in PAIRS if set(pair).issubset(target_set)]
    b_pairs = [pair for pair in PAIRS if set(pair).isdisjoint(target_set)]
    assert len(a_pairs) == 3
    assert len(b_pairs) == 210

    a_local_ranks = {gf2_rank(a_rows(pair, TARGET)) for pair in a_pairs}
    b_local_ranks = {gf2_rank(b_rows(pair, TARGET)) for pair in b_pairs}
    assert a_local_ranks == {H - 3}
    assert b_local_ranks == {H - 2}
    assert {len(a_rows(pair, TARGET)) for pair in a_pairs} == {H - 3}
    assert {len(b_rows(pair, TARGET)) for pair in b_pairs} == {1540 - 1}

    # The target-local A family lies in the target hyperplane (rank 23), while
    # the B family joins to the full active factor (rank 24).
    a_join_rank = gf2_rank([row for pair in a_pairs for row in a_rows(pair, TARGET)])
    b_join_rank = gf2_rank([row for pair in b_pairs for row in b_rows(pair, TARGET)])
    assert a_join_rank == H - 1
    assert b_join_rank == H

    # For a fixed pair, all target-excluded source spans recover the full
    # pair span.  The rank is checked on every pair using a canonical target
    # coordinate k outside the pair; coordinate symmetry handles the target
    # choice, while the Lean theorem records the generic statement.
    full_pair_ranks = set()
    excluded_pair_ranks = set()
    for pair in PAIRS:
        pair_set = set(pair)
        target_k = next(i for i in range(H) if i not in pair_set)
        target = tuple(sorted((*pair, target_k)))
        rows = a_rows(pair, target)
        full_rows = [TRIPLE_MASKS[triple] for triple in TRIPLES if pair_set.issubset(triple)]
        full_pair_ranks.add(gf2_rank(full_rows))
        excluded_pair_ranks.add(gf2_rank(rows))
    assert full_pair_ranks == {H - 2}
    assert excluded_pair_ranks == {H - 3}

    # Existing pair/complement conditional width and aggregate-wise ledger.
    v = len(TRIPLES)
    n0 = v**3
    i0 = 3 * v**2
    m = H**3
    pair_count = len(PAIRS)
    width = 2 * n0 + i0 * (2 * pair_count + H)
    padding = 2**35
    centre_saving = 2 * n0 - 2 * i0 * H**2
    normalized = Fraction(centre_saving, m * padding)
    aggregate_count = 2 * pair_count
    three_stage_cost_per_aggregate = H * (1 + H + H**2)
    all_bank_three_stage_cost = aggregate_count * three_stage_cost_per_aggregate
    target_local_aggregate_count = len(a_pairs) + len(b_pairs)
    target_local_three_stage_cost = target_local_aggregate_count * three_stage_cost_per_aggregate

    assert width == 23661822976
    assert centre_saving == 2425172992
    assert normalized == Fraction(2368333, 463856467968)
    assert normalized > Fraction(1, 10**9)
    assert three_stage_cost_per_aggregate == 14424
    assert all_bank_three_stage_cost == 7962048
    assert target_local_three_stage_cost == 3072312

    return {
        "h": H,
        "target": TARGET,
        "A_pair_count": len(a_pairs),
        "B_pair_count": len(b_pairs),
        "A_local_source_count": H - 3,
        "B_local_source_count": 1540 - 1,
        "A_local_rank": sorted(a_local_ranks),
        "B_local_rank": sorted(b_local_ranks),
        "A_target_join_rank": a_join_rank,
        "B_target_join_rank": b_join_rank,
        "full_pair_span_rank": sorted(full_pair_ranks),
        "diagonal_excluded_A_span_rank": sorted(excluded_pair_ranks),
        "pair_count": pair_count,
        "width": width,
        "padding": padding,
        "centre_saving": centre_saving,
        "normalized_margin": str(normalized),
        "normalized_margin_float": float(normalized),
        "three_stage_cost_per_aggregate": three_stage_cost_per_aggregate,
        "all_bank_three_stage_cost": all_bank_three_stage_cost,
        "target_local_aggregate_count": target_local_aggregate_count,
        "target_local_three_stage_cost": target_local_three_stage_cost,
        "interpretation": (
            "conditional pair/complement aggregate-wise ledger; no physical "
            "complex gate or all-length theorem"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
