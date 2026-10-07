#!/usr/bin/env python3
"""Audit target-dependent pair-prefix label spans over F_2.

For a fixed pair F={0,1}, let S_k be the span of triple indicators
F union {l} with l != k.  These are the diagonal-excluded source spans for
the targets F union {k}.  The script computes their ranks and the dimension
of their common intersection.  This is a local frame-reuse audit, not a
linear-circuit verifier.
"""
import argparse
from itertools import combinations


def indicator(t):
    z = 0
    for i in t:
        z |= 1 << i
    return z


def row_basis(rows):
    basis = {}
    for row in rows:
        x = row
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return list(basis.values())


def rank(rows):
    return len(row_basis(rows))


def nullspace(equations, nvars):
    """Return a basis of {x : equation dot x = 0} as bit masks."""
    rows = list(equations)
    pivots = []
    r = 0
    for col in range(nvars):
        pivot = next((j for j in range(r, len(rows))
                      if (rows[j] >> col) & 1), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for j in range(len(rows)):
            if j != r and ((rows[j] >> col) & 1):
                rows[j] ^= rows[r]
        pivots.append(col)
        r += 1
    free = [c for c in range(nvars) if c not in pivots]
    out = []
    for f in free:
        x = 1 << f
        for row, p in reversed(list(zip(rows[:r], pivots))):
            if bin(row & x).count("1") & 1:
                x |= 1 << p
        out.append(x)
    return out


def intersection_basis(u, v, width):
    """Basis of the intersection of two row spaces."""
    u = row_basis(u)
    v = row_basis(v)
    equations = []
    for bit in range(width):
        eq = 0
        for j, row in enumerate(u):
            if (row >> bit) & 1:
                eq |= 1 << j
        for j, row in enumerate(v):
            if (row >> bit) & 1:
                eq |= 1 << (len(u) + j)
        equations.append(eq)
    coeff_basis = nullspace(equations, len(u) + len(v))
    vectors = []
    for coeff in coeff_basis:
        z = 0
        for j, row in enumerate(u):
            if (coeff >> j) & 1:
                z ^= row
        vectors.append(z)
    return row_basis(vectors)


def main(h):
    fixed = (0, 1)
    outside = list(range(2, h))
    spans = []
    for k in outside:
        rows = [indicator((*fixed, ell)) for ell in outside if ell != k]
        spans.append(rows)
    common = row_basis(spans[0])
    print({"h": h, "fixed_pair": fixed,
           "target_count": len(outside),
           "each_target_span_rank": rank(spans[0])})
    for rows in spans[1:]:
        common = intersection_basis(common, rows, h)
    print({"common_intersection_rank": len(common),
           "interpretation": "fixed-label reuse across all targets"})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--h", type=int, default=24)
    main(parser.parse_args().h)
