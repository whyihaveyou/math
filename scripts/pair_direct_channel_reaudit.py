#!/usr/bin/env python3
"""h=24 re-audit of the pair-only direct-channel budget.

The pair/complement scalar identity supplies the diagonal-free coefficient
``(1-r)/2`` (``r = |S ∩ T|``).  The missing ``r=3`` coefficient is the
direct source value ``x_S``.  This script only recomputes the integer ledger
for that direct channel; the algebraic no-go and the identity-factorisation
rank statement live in the Lean files named in the report.

The one-way and two-way charges are deliberately reported separately.  A
one-way charge of one frame unit per direct coordinate is already enough to
make the h=24 margin negative.  The existing pair-complement boundary audit
uses two units (rise and return), which is more negative.  These are route
specific accounting premises, not universal lower bounds on arbitrary
circuits.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


H = 24
V = comb(H, 3)
I0 = 3 * V**2
M = H**3
CENTRE_SAVING = 2_425_172_992
PAIR_PADDING = 2**35
DIRECT_COUNT = I0 * V


def audit() -> dict[str, object]:
    assert V == 2024
    assert I0 == 12_289_728
    assert DIRECT_COUNT == 24_874_409_472
    assert CENTRE_SAVING == 2_425_172_992
    # The scalar pair/complement role count is 23,661,822,976, so its
    # next power-of-two bucket is 2^35.
    pair_width = 23_661_822_976
    assert 2**34 < pair_width <= PAIR_PADDING

    def line(charge: int) -> dict[str, object]:
        margin = CENTRE_SAVING - charge * DIRECT_COUNT
        normalized = Fraction(margin, M * PAIR_PADDING)
        return {
            "per_direct_coordinate_charge": charge,
            "charge": charge * DIRECT_COUNT,
            "margin": margin,
            "normalized_margin": str(normalized),
            "normalized_margin_float": float(normalized),
        }

    # A nonnegative margin would require an average charge strictly below one
    # unit here: Δ / (I0*V) is < 1.  Since the charge is integral in this
    # ledger, only the uncharged (and therefore purely conditional) line can
    # remain nonnegative.
    break_even_ratio = Fraction(CENTRE_SAVING, DIRECT_COUNT)
    assert break_even_ratio < 1
    assert line(0)["margin"] == CENTRE_SAVING
    assert line(1)["margin"] == -22_449_236_480
    assert line(2)["margin"] == -47_323_645_952
    assert line(2)["normalized_margin"] == "-23107249/231928233984"

    return {
        "h": H,
        "triple_count": V,
        "invocations": I0,
        "centre_saving": CENTRE_SAVING,
        "pair_width": pair_width,
        "pair_padding": PAIR_PADDING,
        "direct_coordinates": DIRECT_COUNT,
        "break_even_average_charge": str(break_even_ratio),
        "ledgers": {
            "uncharged": line(0),
            "one_way": line(1),
            "two_way": line(2),
        },
        "scope": (
            "h24 integer accounting; algebraic pair no-go is Lean-checked, "
            "but no universal circuit lower bound is claimed"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
