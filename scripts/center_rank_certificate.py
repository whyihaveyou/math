#!/usr/bin/env python3
"""Exact rank certificate for the h=24 compressed centre map.

For a source triple T, the compressed centre map sends its basis vector to

    v_T[i] = 1_{i in T} - 1/3.

This is the column matrix of ``CenterCompression.compressedG`` over any
characteristic-zero field.  The script uses exact rational arithmetic, records
one explicit 24-by-24 minor, and checks its determinant.  A nonzero minor
proves that the map has rank 24 and is therefore surjective onto the h=24
centre bank.

The conclusion is deliberately scoped: it rules out any further *linear*
centre-only reduction that must reproduce compressedG on arbitrary triple
inputs.  It does not rule out a nonlinear implementation or a different
factorisation whose intermediate coordinates are not the centre output.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Iterable, Sequence

H = 24
TRIPLES = tuple(combinations(range(H), 3))


def compressed_column(triple: tuple[int, ...], h: int = H) -> tuple[Fraction, ...]:
    """The exact compressedG image of the basis vector at ``triple``."""
    return tuple(Fraction((1 if i in triple else 0), 1) - Fraction(1, 3)
                 for i in range(h))


def rank_fraction(rows: Sequence[Sequence[Fraction]]) -> int:
    """Gaussian elimination over Q, with no floating-point arithmetic."""
    a = [list(row) for row in rows]
    if not a:
        return 0
    m, n = len(a), len(a[0])
    rank = 0
    for col in range(n):
        pivot = next((r for r in range(rank, m) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        p = a[rank][col]
        a[rank] = [x / p for x in a[rank]]
        for r in range(m):
            if r == rank or not a[r][col]:
                continue
            q = a[r][col]
            a[r] = [x - q * y for x, y in zip(a[r], a[rank])]
        rank += 1
        if rank == m:
            break
    return rank


def determinant_fraction(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    """Determinant by fraction-preserving pivot elimination."""
    a = [list(row) for row in matrix]
    n = len(a)
    assert all(len(row) == n for row in a)
    det = Fraction(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        p = a[col][col]
        det *= p
        for r in range(col + 1, n):
            if not a[r][col]:
                continue
            q = a[r][col] / p
            for c in range(col + 1, n):
                a[r][c] -= q * a[col][c]
    return det


def chosen_columns() -> tuple[tuple[int, ...], ...]:
    """A simple explicit full-rank minor.

    There are 22 columns (0,1,k), k=2,...,23, followed by two replacement
    columns.  This list is kept explicit in the output so the certificate is
    independently reproducible.
    """
    return tuple((0, 1, k) for k in range(2, H)) + ((0, 2, 3), (1, 2, 3))


def audit() -> dict[str, object]:
    columns = tuple(compressed_column(t) for t in TRIPLES)
    # Convert column storage to the row storage expected by rank_fraction.
    matrix = tuple(tuple(columns[c][r] for c in range(len(columns)))
                   for r in range(H))
    selected = chosen_columns()
    indices = tuple(TRIPLES.index(t) for t in selected)
    minor = tuple(tuple(matrix[r][c] for c in indices) for r in range(H))
    determinant = determinant_fraction(minor)
    rank = rank_fraction(matrix)
    expected_det = Fraction(5)
    assert len(TRIPLES) == 2024
    assert len(selected) == H
    assert determinant == expected_det
    assert rank == H
    return {
        "h": H,
        "domain_triple_count": len(TRIPLES),
        "matrix_shape": (H, len(TRIPLES)),
        "selected_columns": selected,
        "minor_determinant": str(determinant),
        "rank_over_Q": rank,
        "surjective_to_centre_bank": rank == H,
        "kernel_dimension_over_Q": len(TRIPLES) - rank,
        "scope": (
            "linear centre-only maps reproducing compressedG on arbitrary "
            "triple inputs; nonlinear or differently factored circuits are "
            "outside this certificate"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
