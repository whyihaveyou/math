#!/usr/bin/env python3
"""Exact h-parameter and padding-bucket audit for the research ledgers.

The first ledger is the conditional q-free side-reuse arithmetic used in
``conditional_side_reuse_ledger.py``.  It reuses the h-dimensional compressed
centre readout for the q-free side moment.  The second ledger is the generic
fused-boundary arithmetic used by ``fused_margin_scan.py``.  Neither ledger is
a circuit theorem: the first leaves the direct ``x_S`` channel unbudgeted and
the second assumes its stated boundary/shear charge.

This independent scan is useful because changing h can cross a power-of-two
width bucket.  It reports h=24 and h=30 exactly, and records the direct-channel
margin so an arithmetic improvement is not confused with a full schedule.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


ONE_E9 = Fraction(1, 10**9)


def next_pow2(value: int) -> int:
    if value <= 0:
        raise ValueError("width must be positive")
    return 1 << (value - 1).bit_length()


def side_reuse_row(h: int) -> dict[str, int | Fraction]:
    """Conditional q-free side-reuse width and exact normalized saving."""

    v = comb(h, 3)
    n0 = v**3
    i0 = 3 * v**2
    width = 2 * n0 + 2 * i0 * h
    padding = next_pow2(width)
    saving = 2 * n0 - 2 * i0 * h**2
    direct_penalty = 2 * i0 * v
    denominator = h**3 * padding
    return {
        "h": h,
        "v": v,
        "N0": n0,
        "I0": i0,
        "width": width,
        "padding": padding,
        "saving": saving,
        "normalized": Fraction(saving, denominator),
        "direct_penalty": direct_penalty,
        "direct_margin": saving - direct_penalty,
        "direct_normalized": Fraction(saving - direct_penalty, denominator),
    }


def fused_boundary_row(h: int, phase_count: int = 6) -> dict[str, int | Fraction]:
    """Generic one-/six-phase fused-boundary arithmetic audit."""

    v = comb(h, 3)
    d = comb(h - 3, 3) + 3 * (h - 3)
    n0 = v**3
    i0 = 3 * v**2
    width = 2 * n0 + i0 * (v * d + h + 1)
    padding = next_pow2(width)
    saving = 2 * n0 - 4 * v**2 * h**2
    shear = i0 * h
    margin = saving - phase_count * shear
    denominator = h**3 * padding
    return {
        "h": h,
        "v": v,
        "neighbor_degree": d,
        "width": width,
        "padding": padding,
        "saving": saving,
        "shear": shear,
        "phase_count": phase_count,
        "margin": margin,
        "normalized": Fraction(margin, denominator),
    }


def main() -> None:
    rows = {h: side_reuse_row(h) for h in (24, 30)}
    for h in (24, 30):
        row = rows[h]
        print({
            "ledger": "conditional_q_free_side_reuse",
            "h": h,
            "v": row["v"],
            "width": row["width"],
            "padding": row["padding"],
            "saving": row["saving"],
            "normalized": str(row["normalized"]),
            "normalized_float": float(row["normalized"]),
            "direct_penalty": row["direct_penalty"],
            "direct_margin": row["direct_margin"],
            "direct_normalized": str(row["direct_normalized"]),
        })

    # These exact checks pin the bucket crossing and prevent accidental use of
    # a floating-point or stale h=24 constant in future audits.
    assert rows[24]["padding"] == 2**34
    assert rows[30]["padding"] == 2**37
    assert rows[24]["normalized"] == Fraction(2368333, 231928233984)
    assert rows[30]["normalized"] == Fraction(700553, 57982058496)
    assert rows[30]["normalized"] > rows[24]["normalized"] > ONE_E9
    assert rows[24]["direct_margin"] < 0
    assert rows[30]["direct_margin"] < 0

    for phase_count in (1, 6):
        for h in (24, 30):
            row = fused_boundary_row(h, phase_count)
            print({
                "ledger": "conditional_fused_boundary",
                "h": h,
                "phase_count": phase_count,
                "width": row["width"],
                "padding": row["padding"],
                "margin": row["margin"],
                "normalized": str(row["normalized"]),
                "normalized_float": float(row["normalized"]),
            })

    six_24 = fused_boundary_row(24, 6)
    six_30 = fused_boundary_row(30, 6)
    assert six_24["normalized"] == Fraction(2624369, 237494511599616)
    assert six_30["normalized"] == Fraction(8200591, 3799912185593856)
    assert six_30["normalized"] > ONE_E9

    scan = [(side_reuse_row(h)["normalized"], h) for h in range(3, 1001)]
    best = max(scan)
    print({
        "ledger": "conditional_q_free_side_reuse",
        "scan_range": "3..1000",
        "best_normalized": str(best[0]),
        "best_h": best[1],
        "scope": "arithmetic and padding only; no direct x_S schedule or all-length theorem",
    })


if __name__ == "__main__":
    main()
