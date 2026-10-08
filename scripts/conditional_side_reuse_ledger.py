#!/usr/bin/env python3
"""Exact H24 ledger for conditional q-free side reuse.

This script is an arithmetic audit only.  It assumes that the q-free side
correction can reuse the compressed centre readout.  It does not construct a
frame-compatible complex gate or a global schedule for the direct x_S term.
"""
from fractions import Fraction
from math import comb

H = 24
V = comb(H, 3)
M = H**3
I0 = 3 * V * V
N0 = V**3
CENTRE_SAVING = 2 * N0 - 2 * I0 * H * H
REUSED_ROLE_COUNT = 2 * N0 + I0 * H
PADDING = 2**34
LOWER_BUCKET = 2**33
PREVIOUS_PADDING = 2**35
DIRECT_PENALTY = 2 * I0 * V
DIRECT_MARGIN = CENTRE_SAVING - DIRECT_PENALTY

assert V == 2024
assert REUSED_ROLE_COUNT == 16877893120
assert LOWER_BUCKET < REUSED_ROLE_COUNT <= PADDING
assert PADDING < PREVIOUS_PADDING
assert DIRECT_MARGIN == -47323645952

print({
    "h": H,
    "triple_count": V,
    "centre_saving": CENTRE_SAVING,
    "reused_role_count": REUSED_ROLE_COUNT,
    "padding": PADDING,
    "same_padding_bucket": True,
    "conditional_normalized_saving": str(Fraction(CENTRE_SAVING, M * PADDING)),
    "direct_diagonal_penalty": DIRECT_PENALTY,
    "direct_diagonal_margin": DIRECT_MARGIN,
    "scope": "conditional q-free side reuse; no physical direct x_S gate or all-length schedule",
})
