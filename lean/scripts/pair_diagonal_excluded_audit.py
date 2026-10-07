#!/usr/bin/env python3
"""Reproduce the local pair-prefix rank audit at a chosen h (default 24).

This is a finite-field geometry check, not a circuit verifier.  Vectors are
triple indicators in F_2^24 and rank is computed by Gaussian elimination.
"""
import argparse
from itertools import combinations
from fractions import Fraction
from math import comb, log

def indicator(t):
    z = 0
    for i in t:
        z |= 1 << i
    return z

def gf2_rank(rows, width):
    rows = list(rows)
    rank = 0
    for bit in range(width):
        pivot = next((j for j in range(rank, len(rows))
                      if (rows[j] >> bit) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and ((rows[j] >> bit) & 1):
                rows[j] ^= rows[rank]
        rank += 1
    return rank

def parity_dot(x, y):
    return bin(x & y).count("1") & 1

def main(h):
    triples = list(combinations(range(h), 3))
    S = (0, 1, 2)
    rows = []
    print(f"h={h}; triple_count={len(triples)}")
    for F in combinations(S, 2):
        source = [t for t in triples if set(F).issubset(t)]
        excluded = [t for t in source if t != S]
        source_rank = gf2_rank(map(indicator, source), h)
        excluded_rank = gf2_rank(map(indicator, excluded), h)
        orthogonal = all(parity_dot(indicator(t), indicator(S)) == 0
                         for t in excluded)
        rows.extend(indicator(t) for t in excluded)
        print({"pair": F, "source_count": len(source),
               "source_rank": source_rank,
               "excluded_count": len(excluded),
               "excluded_rank": excluded_rank,
               "excluded_in_S_perp": orthogonal})
    print({"three_pair_excluded_union_rank": gf2_rank(rows, h),
           "target_perp_dimension": h - 1})

    v = comb(h, 3)
    N0 = v ** 3
    I0 = 3 * v ** 2
    pair_count = comb(h, 2)
    role_count = 2 * N0 + I0 * (pair_count + h)
    padding = 1 << (role_count - 1).bit_length()
    centre_delta = 2 * N0 - 2 * I0 * h ** 2
    one_transition_penalty = (v ** 2) * pair_count * 2
    effective = centre_delta - one_transition_penalty
    normalized = Fraction(effective, h ** 3 * padding)
    recurrence_gap = 1 - log(h ** 3 - effective / padding) / log(h ** 3)
    print({"v": v, "N0": N0, "I0": I0, "pair_count": pair_count,
           "role_count": role_count, "padding": padding,
           "centre_delta": centre_delta,
           "one_transition_codim2_penalty": one_transition_penalty,
           "effective_saving": effective,
           "normalized_saving": str(normalized),
           "normalized_saving_decimal": float(normalized),
           "recurrence_gap_decimal": recurrence_gap})

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--h", type=int, default=24)
    args = parser.parse_args()
    main(args.h)
