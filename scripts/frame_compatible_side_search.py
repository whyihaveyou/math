#!/usr/bin/env python3
"""Exact finite audit of a target-aware even-pair side grouping.

This is a search/audit script, not a circuit verifier.  It checks the scalar
coefficient count and the binary (GF(2)) frame dimensions for one target
triple at ``h=24``.  The proposed grouping keeps only the even intersection
classes used by the original side map:

* ``C2`` consists of pairs contained in the target (three pairs); a grouped
  source label is ``F ∪ {k}`` with ``k`` outside the target, so the target
  triple itself is excluded.
* ``C0`` consists of pairs disjoint from the target (210 pairs); a grouped
  source label is ``F ∪ {k}`` with ``k`` outside the target and outside ``F``.

For a source triple with intersection ``r`` with the target, the restricted
pair counts are ``1`` for ``r=2`` and ``3`` for ``r=0``.  Thus weights
``-1/2`` and ``+1/6`` reproduce the two nonzero coefficients of the original
side correction.  The restriction on the third coordinate is target-aware;
without it a disjoint pair also sees ``r=1`` sources.

The final cost numbers intentionally include two models.  The optimistic
model charges two directional units per grouped pair.  The conditional
codimension model charges two directions for the codimension of the
target-restricted span inside the all-third-coordinate pair span.  Neither
model proves that a frame-labelled circuit exists or gives a lower bound for
arbitrary networks.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


H = 24
TARGET = frozenset((0, 1, 2))


def gf2_rank(rows: list[int]) -> int:
    """Return the rank of bit-vector rows over ``F_2``."""

    basis: dict[int, int] = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                basis[pivot] = value
                break
            value ^= old
    return len(basis)


def indicator(subset: frozenset[int] | tuple[int, ...]) -> int:
    value = 0
    for coordinate in subset:
        value |= 1 << coordinate
    return value


def pair_span(pair: tuple[int, int]) -> list[int]:
    """All triple indicators containing ``pair`` (the shared pair frame)."""

    return [
        indicator(frozenset(pair) | {third})
        for third in range(H)
        if third not in pair
    ]


def restricted_span(pair: tuple[int, int], intersection: int) -> list[int]:
    """Labels ``pair ∪ {k}`` whose intersection with TARGET is ``intersection``."""

    return [
        indicator(frozenset(pair) | {third})
        for third in range(H)
        if third not in pair
        and len((frozenset(pair) | {third}) & TARGET) == intersection
    ]


def verify_scalar_identity() -> dict[int, tuple[int, int, Fraction]]:
    """Check the restricted pair coefficient for every source triple.

    The returned tuple is ``(number of C0 pairs, number of C2 pairs,
    reconstructed coefficient)`` indexed by the intersection cardinality.
    """

    result: dict[int, tuple[int, int, Fraction]] = {}
    for source in combinations(range(H), 3):
        source_set = frozenset(source)
        intersection = len(source_set & TARGET)
        c0 = sum(
            1
            for pair in combinations(range(H), 2)
            if frozenset(pair).isdisjoint(TARGET)
            and frozenset(pair).issubset(source_set)
            and intersection == 0
        )
        c2 = sum(
            1
            for pair in combinations(TARGET, 2)
            if frozenset(pair).issubset(source_set)
            and intersection == 2
        )
        coefficient = Fraction(c0, 6) - Fraction(c2, 2)
        expected = Fraction(1, 2) if intersection == 0 else (
            -Fraction(1, 2) if intersection == 2 else Fraction(0)
        )
        # The target itself is deliberately excluded from the side map.
        if source_set == TARGET:
            expected = Fraction(0)
        assert coefficient == expected, (source, intersection, c0, c2, coefficient, expected)
        result.setdefault(intersection, (c0, c2, coefficient))
    return result


def audit() -> dict[str, object]:
    pairs = list(combinations(range(H), 2))
    triples = list(combinations(range(H), 3))
    classes = {
        0: [pair for pair in pairs if frozenset(pair).isdisjoint(TARGET)],
        2: [pair for pair in pairs if frozenset(pair).issubset(TARGET)],
    }
    assert {key: len(value) for key, value in classes.items()} == {0: 210, 2: 3}

    pair_ranks = {pair: gf2_rank(pair_span(pair)) for pair in pairs}
    assert set(pair_ranks.values()) == {H - 2}

    restricted_ranks = {
        0: {pair: gf2_rank(restricted_span(pair, 0)) for pair in classes[0]},
        2: {pair: gf2_rank(restricted_span(pair, 2)) for pair in classes[2]},
    }
    assert set(restricted_ranks[0].values()) == {H - 5}
    assert set(restricted_ranks[2].values()) == {H - 3}

    class_join_ranks = {
        intersection: gf2_rank(
            [row for pair in class_pairs for row in restricted_span(pair, intersection)]
        )
        for intersection, class_pairs in classes.items()
    }
    assert class_join_ranks == {0: 21, 2: 23}

    # Adding the target line is the one extra active direction for each group.
    target_vector = indicator(TARGET)
    target_join_increments = {
        intersection: {
            pair: gf2_rank(restricted_span(pair, intersection) + [target_vector])
            - gf2_rank(restricted_span(pair, intersection))
            for pair in class_pairs
        }
        for intersection, class_pairs in classes.items()
    }
    assert all(set(values.values()) == {1} for values in target_join_increments.values())

    # The old centre-compressed arithmetic, imported as literals to keep this
    # audit independent from Lean build configuration.
    v = 2024
    n0 = v**3
    i0 = 3 * v**2
    m = H**3
    centre_saving = 2 * n0 - 2 * i0 * H**2
    grouped_pair_count = sum(map(len, classes.values()))
    # The 213 groups are target-indexed: every invocation carries one copy
    # for each of the v target triples.  The side bank therefore has v*213
    # aggregate roles, just as the baseline bank has v*dNbr roles.
    role_count = 2 * n0 + i0 * (v * grouped_pair_count + H)
    padding = 1
    while padding < role_count:
        padding <<= 1

    block = v**2
    optimistic_penalty = 2 * block * v * grouped_pair_count
    optimistic_margin = centre_saving - optimistic_penalty
    optimistic_normalized = Fraction(optimistic_margin, m * padding)

    # If every aggregate must leave its shared pair span and return to its
    # target-restricted span, charge two directions for that exact codimension.
    codim0 = (H - 2) - (H - 5)
    codim2 = (H - 2) - (H - 3)
    codim_penalty = 2 * block * v * (len(classes[0]) * codim0 + len(classes[2]) * codim2)
    codim_margin = centre_saving - codim_penalty
    codim_normalized = Fraction(codim_margin, m * padding)

    scalar = verify_scalar_identity()
    return {
        "h": H,
        "target": tuple(sorted(TARGET)),
        "pair_class_counts": {f"C{key}": len(value) for key, value in classes.items()},
        "pair_span_rank": H - 2,
        "restricted_span_rank": {"C0": H - 5, "C2": H - 3},
        "restricted_class_join_rank": {f"C{key}": value for key, value in class_join_ranks.items()},
        "target_line_join_increment": 1,
        "scalar_coefficients_by_intersection": {
            str(key): {"c0": value[0], "c2": value[1], "coefficient": str(value[2])}
            for key, value in sorted(scalar.items())
        },
        "v": v,
        "N0": n0,
        "I0": i0,
        "m": m,
        "grouped_pair_count": grouped_pair_count,
        "role_count": role_count,
        "padding": padding,
        "centre_saving": centre_saving,
        "optimistic_penalty_two_units": optimistic_penalty,
        "optimistic_margin": optimistic_margin,
        "optimistic_normalized_margin": str(optimistic_normalized),
        "codim0": codim0,
        "codim2": codim2,
        "codimension_penalty": codim_penalty,
        "codimension_margin": codim_margin,
        "codimension_normalized_margin": str(codim_normalized),
    }


if __name__ == "__main__":
    import pprint

    pprint.pp(audit(), sort_dicts=False)
