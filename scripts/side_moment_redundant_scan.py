#!/usr/bin/env python3
"""Scan the q-eliminated side-moment width ledger over h.

This is a scalar width stress test.  It uses the exact identity
sum_i a_i = 3 q, so the side and centre banks each have h roles.  The scan
is useful for choosing a parameter point before attempting a frame proof; it
does not assert that any h has a physical direct-input schedule.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


def audit_h(h: int) -> dict[str, object]:
    v = comb(h, 3)
    n0 = v**3
    i0 = 3 * v**2
    width = 2 * n0 + i0 * (2 * h)
    padding = 1
    while padding < width:
        padding <<= 1
    saving = 2 * n0 - 2 * i0 * h**2
    normalized = Fraction(saving, h**3 * padding)
    return {
        "h": h,
        "v": v,
        "width": width,
        "padding": padding,
        "saving": saving,
        "normalized": normalized,
        "normalized_float": float(normalized),
    }


def scan(start: int = 3, stop: int = 64) -> list[dict[str, object]]:
    return [audit_h(h) for h in range(start, stop + 1)]


if __name__ == "__main__":
    rows = scan()
    for row in sorted(rows, key=lambda r: r["normalized"], reverse=True)[:10]:
        print(row)
