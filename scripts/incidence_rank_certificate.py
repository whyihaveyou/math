#!/usr/bin/env python3
"""Exact rank certificate for the h=24 shared incidence feature map.

For a source triple ``T`` let ``a_i(T) = 1_{i in T}``.  The centre map and
the redundant-global side map both factor through the 24-vector ``a``.  This
script exhibits a 24-by-24 minor of that incidence matrix with determinant
``-3`` over ``Q``.  Hence the common incidence feature map has rank exactly
24 (the codomain already has dimension 24), so this particular linear
feature model cannot be compressed to fewer than 24 shared coordinates.

The certificate is deliberately narrow.  It is an exact finite calculation
about the shared incidence factorisation; it is not a lower bound for
arbitrary complex linear circuits, and it does not settle whether a different
factorisation or a frame-compatible direct gate can avoid this feature map.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence


H = 24
TRIPLES = tuple(combinations(range(H), 3))


def determinant_fraction(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    """Compute a determinant over Q by exact pivot elimination."""
    a = [list(row) for row in matrix]
    n = len(a)
    assert n and all(len(row) == n for row in a)
    determinant = Fraction(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            determinant = -determinant
        pivot_value = a[col][col]
        determinant *= pivot_value
        for row in range(col + 1, n):
            if not a[row][col]:
                continue
            multiplier = a[row][col] / pivot_value
            for j in range(col + 1, n):
                a[row][j] -= multiplier * a[col][j]
    return determinant


def rank_fraction(matrix: Sequence[Sequence[Fraction]]) -> int:
    """Compute matrix rank over Q by exact Gaussian elimination."""
    a = [list(row) for row in matrix]
    if not a:
        return 0
    rows, cols = len(a), len(a[0])
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        pivot_value = a[rank][col]
        a[rank] = [entry / pivot_value for entry in a[rank]]
        for row in range(rows):
            if row == rank or not a[row][col]:
                continue
            multiplier = a[row][col]
            a[row] = [x - multiplier * y for x, y in zip(a[row], a[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def selected_columns() -> tuple[tuple[int, ...], ...]:
    """Return 24 explicit source triples used for the nonzero minor.

    The first 22 columns are ``{0,1,k}`` for ``k=2,...,23}``; the final two
    columns are ``{0,2,3}`` and ``{1,2,3}``.  The order is part of the
    certificate because it fixes the determinant sign.
    """
    return tuple((0, 1, k) for k in range(2, H)) + ((0, 2, 3), (1, 2, 3))


def audit() -> dict[str, object]:
    columns = tuple(tuple(Fraction(int(i in triple)) for i in range(H))
                    for triple in TRIPLES)
    matrix = tuple(tuple(columns[column][row]
                         for column in range(len(columns)))
                   for row in range(H))

    selected = selected_columns()
    indices = tuple(TRIPLES.index(triple) for triple in selected)
    minor = tuple(tuple(matrix[row][column] for column in indices)
                  for row in range(H))
    minor_determinant = determinant_fraction(minor)
    full_rank = rank_fraction(matrix)

    assert len(TRIPLES) == 2024
    assert len(selected) == H
    assert minor_determinant == Fraction(-3)
    assert full_rank == H

    return {
        "h": H,
        "domain_triple_count": len(TRIPLES),
        "matrix_shape": (H, len(TRIPLES)),
        "selected_columns": selected,
        "minor_determinant_over_Q": str(minor_determinant),
        "incidence_rank_over_Q": full_rank,
        "shared_feature_dimension": H,
        "no_fewer_than_24_in_this_linear_model": full_rank == H,
        "scope": (
            "shared incidence factorisation only; no arbitrary-circuit lower "
            "bound and no physical frame schedule claim"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
