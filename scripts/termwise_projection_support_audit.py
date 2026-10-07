#!/usr/bin/env python3
"""Conditional termwise support bound for oblique projections.

Assume a rank-h projection P is written as h rank-one terms U_i V_i, and
assume each term is itself frame-compatible: every nonzero row/column pair
has even triple intersection (with diagonal allowed).  The diagonal support of
one term is then a pairwise-even family of triples.  The elementary 3-set
forbidden-intersection-1 bound gives size <= h-2, so at most h*(h-2) diagonal
entries of P can be nonzero.  This is explicitly a termwise/no-cancellation
premise; it does not cover cancellations among dense rank-one terms.
"""
from fractions import Fraction
from math import comb

h = 24
v = comb(h, 3)
N0 = v**3
I0 = 3 * v**2
m = h**3
centre_saving = 2 * N0 - 2 * I0 * h**2
max_diagonal_P = h * (h - 2)
min_diagonal_Q = v - max_diagonal_P
penalty = 2 * I0 * min_diagonal_Q
margin = centre_saving - penalty
padding = 2**36
print({
    "h": h,
    "v": v,
    "rank_P": h,
    "per_term_diagonal_support_bound": h - 2,
    "max_diagonal_P_support": max_diagonal_P,
    "min_diagonal_residual_support": min_diagonal_Q,
    "centre_saving": centre_saving,
    "conditional_penalty": penalty,
    "conditional_margin": margin,
    "conditional_normalized_margin": str(Fraction(margin, m * padding)),
    "conditional_normalized_margin_float": float(Fraction(margin, m * padding)),
})
