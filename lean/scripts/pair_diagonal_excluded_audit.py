#!/usr/bin/env python3
"""Reproduce the local pair-prefix rank audit at h=24.

This is a finite-field geometry check, not a circuit verifier.  Vectors are
triple indicators in F_2^24 and rank is computed by Gaussian elimination.
"""
from itertools import combinations
from fractions import Fraction
from math import comb, log

H = 24
TRIPLES = list(combinations(range(H), 3))

def indicator(t):
    z = 0
    for i in t:
        z |= 1 << i
    return z

def gf2_rank(rows):
    rows = list(rows)
    rank = 0
    for bit in range(H):
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

def main():
    S = (0, 1, 2)
    rows = []
    print(f"h={H}; triple_count={len(TRIPLES)}")
    for F in combinations(S, 2):
        source = [t for t in TRIPLES if set(F).issubset(t)]
        excluded = [t for t in source if t != S]
        source_rank = gf2_rank(map(indicator, source))
        excluded_rank = gf2_rank(map(indicator, excluded))
        orthogonal = all(parity_dot(indicator(t), indicator(S)) == 0
                         for t in excluded)
        rows.extend(indicator(t) for t in excluded)
        print({"pair": F, "source_count": len(source),
               "source_rank": source_rank,
               "excluded_count": len(excluded),
               "excluded_rank": excluded_rank,
               "excluded_in_S_perp": orthogonal})
    print({"three_pair_excluded_union_rank": gf2_rank(rows),
           "target_perp_dimension": H - 1})

    v = comb(H, 3)
    N0 = v ** 3
    I0 = 3 * v ** 2
    pair_count = comb(H, 2)
    role_count = 2 * N0 + I0 * (pair_count + H)
    padding = 2 ** 35
    centre_delta = 2 * N0 - 2 * I0 * H ** 2
    one_transition_penalty = (v ** 2) * pair_count * 2
    effective = centre_delta - one_transition_penalty
    normalized = Fraction(effective, H ** 3 * padding)
    recurrence_gap = 1 - log(H ** 3 - effective / padding) / log(H ** 3)
    print({"v": v, "N0": N0, "I0": I0, "pair_count": pair_count,
           "role_count": role_count, "padding": padding,
           "centre_delta": centre_delta,
           "one_transition_codim2_penalty": one_transition_penalty,
           "effective_saving": effective,
           "normalized_saving": str(normalized),
           "normalized_saving_decimal": float(normalized),
           "recurrence_gap_decimal": recurrence_gap})

if __name__ == "__main__":
    main()
