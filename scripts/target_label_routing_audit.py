#!/usr/bin/env python3
"""Exact cover and conditional route ledger for singleton target labels.

For a target triple ``S`` and a singleton label ``e_i`` the boundary test is

    e_i in t_S^perp  <=>  i not in S.

Consequently a fixed set ``C`` of singleton labels covers every target triple
iff ``C`` has at least four distinct coordinates: a triple can contain all of
three chosen coordinates, while it cannot contain all four.  The Lean file
``TargetLabelCover.lean`` proves the corresponding label-level statement for
all ``h >= 4``.

This script keeps the physical question separate from that finite cover.  It
reports three explicitly conditional route ledgers at ``h=24``:

* ``free_cover`` charges no directions for selecting an eligible label;
* ``switch_only`` charges two directions for each switch between the four
  singleton frames (three switches in a four-block pass);
* ``block_roundtrip`` charges a full-active -> singleton -> full excursion for
  each of the four frame blocks;
* ``target_roundtrip`` charges that excursion separately for every target.

The latter two are deliberately conservative accounting premises, while the
first is only the zero-charge target-labelled-routing premise.  None of these
ledgers proves a complex gate, a simultaneous schedule, or an all-length DFT
recurrence.  The base width is inherited from the 24 singleton-incidence side
candidate; an optional ``explicit_frame_slots`` line shows the effect of
charging four extra frame slots as scalar roles.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb


def next_pow2(value: int) -> int:
    if value <= 0:
        raise ValueError("width must be positive")
    return 1 << (value - 1).bit_length()


def choose(n: int, r: int) -> int:
    """A zero-safe binomial used for the h-parameter scan."""

    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def cover_size_minimal(h: int) -> int:
    """Minimum number of distinct singleton labels covering all triples."""

    if h < 4:
        raise ValueError("the four-singleton cover requires h >= 4")
    return 4


def route_rows(h: int = 24, cover_size: int = 4) -> dict[str, object]:
    if h < 4:
        raise ValueError("h must be at least 4")
    if cover_size < 4:
        raise ValueError("a singleton cover of all triples needs at least four labels")

    cover = tuple(range(cover_size))
    triples = tuple(combinations(range(h), 3))
    v = len(triples)
    i0 = 3 * v**2
    n0 = v**3
    m = h**3
    prefix_sum = 1 + h + h * h

    # A target is eligible for e_i exactly when i is absent from the target.
    eligible_histogram = Counter(
        cover_size - len(set(target).intersection(cover)) for target in triples
    )
    expected_histogram = {
        eligible: choose(cover_size, cover_size - eligible)
        * choose(h - cover_size, 3 - (cover_size - eligible))
        for eligible in range(1, cover_size + 1)
    }
    # The formula above is only nonzero for a feasible intersection class.
    expected_histogram = {
        count: expected_histogram.get(count, 0)
        for count in range(1, cover_size + 1)
        if expected_histogram.get(count, 0)
    }
    assert dict(sorted(eligible_histogram.items())) == dict(
        sorted(expected_histogram.items())
    )
    assert sum(eligible_histogram.values()) == v

    frame_incidence = {
        i: sum(i not in target for target in triples) for i in cover
    }
    assert set(frame_incidence.values()) == {choose(h - 1, 3)}

    # A deterministic balanced assignment: choose the currently least-loaded
    # eligible frame, breaking ties by coordinate.  At h=24,k=4 it gives four
    # equal blocks of 506 targets, making the block ledger reproducible.
    loads = {i: 0 for i in cover}
    assignment: dict[tuple[int, int, int], int] = {}
    for target in triples:
        eligible = [i for i in cover if i not in target]
        chosen = min(eligible, key=lambda i: (loads[i], i))
        assignment[target] = chosen
        loads[chosen] += 1
    assert sum(loads.values()) == v

    # This is the scalar width of the existing singleton-incidence candidate;
    # singleton labels are address metadata, so no extra role is charged here.
    base_width = 2 * n0 + i0 * (2 * h)
    base_padding = next_pow2(base_width)
    centre_saving = 2 * n0 - 2 * i0 * h * h

    # Three finite prefixes have sizes 1, h, h^2.  The charge conventions are
    # intentionally named so a future gate proof can replace them explicitly.
    free_cover = 0
    switch_only = 2 * (cover_size - 1) * prefix_sum
    block_roundtrip = 2 * (h - 1) * cover_size * prefix_sum
    target_roundtrip = 2 * (h - 1) * v * prefix_sum

    route_charges = {
        "free_cover": free_cover,
        "switch_only": switch_only,
        "block_roundtrip": block_roundtrip,
        "target_roundtrip": target_roundtrip,
    }
    ledgers = {
        name: {
            "route_charge": charge,
            "margin": centre_saving - charge,
            "normalised_margin": str(
                Fraction(centre_saving - charge, m * base_padding)
            ),
            "normalised_margin_float": float(
                Fraction(centre_saving - charge, m * base_padding)
            ),
        }
        for name, charge in route_charges.items()
    }

    # Optional sensitivity line: charging four frame slots as scalar roles
    # crosses h=24 from 2^34 to 2^35.  This is not part of the base ledger.
    explicit_slot_width = base_width + i0 * cover_size
    explicit_slot_padding = next_pow2(explicit_slot_width)
    explicit_slot_ledgers = {
        name: {
            "route_charge": charge,
            "margin": centre_saving - charge,
            "padding": explicit_slot_padding,
            "normalised_margin": str(
                Fraction(centre_saving - charge, m * explicit_slot_padding)
            ),
        }
        for name, charge in route_charges.items()
    }

    assert cover_size_minimal(h) == 4
    if h == 24 and cover_size == 4:
        assert v == 2024
        assert dict(sorted(eligible_histogram.items())) == {
            1: 4,
            2: 120,
            3: 760,
            4: 1140,
        }
        assert loads == {0: 506, 1: 506, 2: 506, 3: 506}
        assert base_width == 17_172_846_592
        assert base_padding == 2**34
        assert centre_saving == 2_425_172_992
        assert route_charges == {
            "free_cover": 0,
            "switch_only": 3_606,
            "block_roundtrip": 110_584,
            "target_roundtrip": 55_955_504,
        }

    return {
        "h": h,
        "cover_size": cover_size,
        "minimum_cover_size": cover_size_minimal(h),
        "target_count": v,
        "cover_coordinates": cover,
        "eligible_target_histogram": dict(sorted(eligible_histogram.items())),
        "per_frame_target_incidence": frame_incidence,
        "balanced_assignment_loads": loads,
        "N0": n0,
        "I0": i0,
        "prefix_sum_1_plus_h_plus_h2": prefix_sum,
        "base_width": base_width,
        "base_padding": base_padding,
        "centre_saving": centre_saving,
        "conditional_route_ledgers": ledgers,
        "explicit_frame_slot_width": explicit_slot_width,
        "explicit_frame_slot_padding": explicit_slot_padding,
        "explicit_frame_slot_ledgers": explicit_slot_ledgers,
        "scope": (
            "finite singleton cover and conditional direction accounting; no "
            "complex gate, global schedule, or all-length DFT theorem"
        ),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(route_rows(), sort_dicts=False)
