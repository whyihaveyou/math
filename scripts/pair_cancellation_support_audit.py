#!/usr/bin/env python3
"""Exact support audit for a cancellation-based pair-bank redesign.

Fix S={0,1,2}.  The candidate pair/complement bank exposes

    A_F = sum_{T superset F} x_T       (F subset S),
    B_F = sum_{T disjoint F} x_T       (F disjoint S).

One possible way to avoid the common row-5 P-direction is to replace these
213 values by linear combinations whose source support is contained in
``t_S^perp``.  For a combination w this means that its coefficient is zero
on every source triple T with |S intersect T| odd.  This script checks the
strongest one-shot version: can the diagonal-free side coefficient itself be
written as such a combination?

The answer is no.  The exact rational ranks are

    rank(M_odd) = 211,
    rank([M_odd; A]) = 213,
    rank([M_odd,0; A,y]) = 214,

where A is the aggregate-to-source incidence matrix and y is twice the
diagonal-free side coefficient (1 on r=0, -1 on r=2, and 0 otherwise).
Thus the equations M_odd w=0 and A w=y have no solution over Q.  This is a
conditional obstruction to this cancellation route, not a lower bound on
redesigned networks that add new bank coordinates or use multi-stage copies.
"""

from __future__ import annotations

from itertools import combinations


H = 24
TARGET = frozenset((0, 1, 2))


def incidence_rows() -> tuple[list[list[int]], list[list[int]], list[int]]:
    """Return (A, M_odd, y) for the fixed target."""

    triples = list(combinations(range(H), 3))
    columns = list(combinations(sorted(TARGET), 2)) + [
        pair for pair in combinations(range(H), 2)
        if frozenset(pair).isdisjoint(TARGET)
    ]
    assert len(columns) == 3 + 210

    all_rows: list[list[int]] = []
    odd_rows: list[list[int]] = []
    y: list[int] = []
    for triple in triples:
        source = frozenset(triple)
        intersection = len(source & TARGET)
        row = [
            int(pair_set.issubset(source)) if i < 3 else int(source.isdisjoint(pair_set))
            for i, pair in enumerate(columns)
            for pair_set in (frozenset(pair),)
        ]
        all_rows.append(row)
        if intersection % 2:
            odd_rows.append(row)
        y.append(1 if intersection == 0 else -1 if intersection == 2 else 0)
    return all_rows, odd_rows, y


def rank_mod(rows: list[list[int]], prime: int) -> int:
    """Gaussian rank over F_prime; used as a fast independent check."""

    a = [[x % prime for x in row] for row in rows]
    m = len(a)
    n = len(a[0]) if m else 0
    pivot_row = 0
    for column in range(n):
        found = next((r for r in range(pivot_row, m) if a[r][column]), None)
        if found is None:
            continue
        a[pivot_row], a[found] = a[found], a[pivot_row]
        inverse = pow(a[pivot_row][column], prime - 2, prime)
        a[pivot_row] = [(x * inverse) % prime for x in a[pivot_row]]
        for r in range(pivot_row + 1, m):
            coefficient = a[r][column]
            if coefficient:
                a[r] = [x - coefficient * z for x, z in zip(a[r], a[pivot_row])]
                a[r] = [x % prime for x in a[r]]
        pivot_row += 1
        if pivot_row == m:
            break
    return pivot_row


def exact_ranks() -> tuple[int, int, int]:
    """Compute the three ranks over Q using SymPy's exact DomainMatrix."""

    import sympy as sp

    all_rows, odd_rows, y = incidence_rows()
    to_domain = lambda rows: sp.polys.matrices.DomainMatrix.from_list_sympy(
        len(rows), len(rows[0]), rows
    ).convert_to(sp.QQ)
    odd = to_domain(odd_rows)
    aggregate = to_domain(all_rows)
    stacked = odd.vstack(aggregate)
    augmented = to_domain(
        [row + [0] for row in odd_rows] + [row + [value] for row, value in zip(all_rows, y)]
    )
    return odd.rank(), stacked.rank(), augmented.rank()


def audit() -> dict[str, object]:
    all_rows, odd_rows, y = incidence_rows()
    exact = exact_ranks()
    modular = {
        prime: (
            rank_mod(odd_rows, prime),
            rank_mod(odd_rows + all_rows, prime),
            rank_mod(
                [row + [0] for row in odd_rows]
                + [row + [value] for row, value in zip(all_rows, y)],
                prime,
            ),
        )
        for prime in (3, 1_000_003)
    }
    return {
        "h": H,
        "target": tuple(sorted(TARGET)),
        "aggregate_columns": len(all_rows[0]),
        "source_rows": len(all_rows),
        "odd_support_rows": len(odd_rows),
        "exact_ranks_Q": {
            "M_odd": exact[0],
            "stack_Modd_A": exact[1],
            "augmented": exact[2],
        },
        "modular_rank_checks": modular,
        "no_one_shot_even_support_solution": exact[1] < exact[2],
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
