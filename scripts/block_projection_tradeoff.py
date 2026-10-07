#!/usr/bin/env python3
"""Conditional block-local tradeoff for oblique side projections.

A side bank whose roles stay inside pairwise-even cliques can only mix triples
within a clique.  This script uses a deterministic greedy clique partition at
h=24 and compares coordinate residual blocks with the cheapest rank-one
oblique block model: on a k-clique, a rank-one centre projection can reduce the
residual diagonal support to one entry, but then its rank-(k-1) residual is
supported on k^2-k+1 entries.  It is a conditional block-local audit, not a
lower bound for arbitrary projections with cancellations between blocks.
"""
from collections import Counter
from itertools import combinations

H = 24
TRIPLES = list(combinations(range(H), 3))
remaining = set(TRIPLES)
pairs = list(combinations(range(H), 2))
blocks = []
while remaining:
    counts = {F: 0 for F in pairs}
    for T in remaining:
        for F in combinations(T, 2):
            counts[F] += 1
    F = max(counts, key=counts.get)
    block = {T for T in remaining if set(F) <= set(T)}
    blocks.append(block)
    remaining -= block

sizes = Counter(map(len, blocks))
assert sum(k * n for k, n in sizes.items()) == len(TRIPLES) == 2024
assert all(2 <= k <= 22 for k in sizes)

# Centre rank budget h=24.  Concentrating rank-one centre blocks on the
# largest cliques minimizes the remaining diagonal support.
rank_budget = H
chosen = []
for k in sorted(sizes, reverse=True):
    take = min(sizes[k], rank_budget - len(chosen))
    chosen.extend([k] * take)
    if len(chosen) == rank_budget:
        break
assert len(chosen) == rank_budget
covered = sum(chosen)
# For each selected k-clique, oblique rank-one centre projection leaves a
# rank-(k-1) residual with one nonzero diagonal and k^2-k+1 support entries.
diag_oblique = len(TRIPLES) - (covered - rank_budget)
support_oblique = sum(k * k - k + 1 for k in chosen) + (len(TRIPLES) - covered)
# Coordinate blocks keep exactly rank_budget centre coordinates and have a
# residual diagonal on every other coordinate.
diag_coordinate = len(TRIPLES) - rank_budget
support_coordinate = diag_coordinate

I0 = 3 * len(TRIPLES) ** 2
centre_saving = 2 * len(TRIPLES) ** 3 - 2 * I0 * H**2
positive_diag_bound = (centre_saving - 1) // (2 * I0)
padding = 2**36
side_budget = (padding - 2 * len(TRIPLES) ** 3) // I0 - H

print({
    "h": H,
    "v": len(TRIPLES),
    "greedy_block_size_histogram": dict(sorted(sizes.items(), reverse=True)),
    "block_count": len(blocks),
    "centre_rank_budget": rank_budget,
    "oblique_selected_block_sizes": chosen,
    "oblique_diag_roles_lower_model": diag_oblique,
    "oblique_support_roles_lower_model": support_oblique,
    "coordinate_diag_roles": diag_coordinate,
    "coordinate_support_roles": support_coordinate,
    "centre_saving": centre_saving,
    "positive_diag_bound": positive_diag_bound,
    "side_role_budget_at_2^36": side_budget,
})
