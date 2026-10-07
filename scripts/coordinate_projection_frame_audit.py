#!/usr/bin/env python3
"""Audit a rank-h coordinate projection for the centre/side split.

The scalar identity RG + JV = I permits a trivial decomposition of the
triple-coordinate space X: keep h selected triples in the centre bank and put
the remaining v-h coordinates in the side bank.  This script verifies the
projection ranks and computes the h=24 role arithmetic.  It also checks the
published frame adjacency condition: side roles are only allowed for distinct
triples with even intersection.  The coordinate residual has diagonal entries
on every unselected triple, so it cannot be represented by those roles.
"""
from fractions import Fraction
from itertools import combinations

H = 24
TRIPLES = list(combinations(range(H), 3))
V = len(TRIPLES)
SELECTED = set(TRIPLES[:H])  # any H distinct triples give the same rank result

# Coordinate matrices are represented by their diagonal supports.
P_diag = [int(T in SELECTED) for T in TRIPLES]
J_diag = [1 - p for p in P_diag]
assert all(p * p == p for p in P_diag)
assert all(j * j == j for j in J_diag)
assert sum(P_diag) == H
assert sum(J_diag) == V - H
assert sum(J_diag) == V - H  # trace(J)=rank(J) for an idempotent over C

# The published side role relation (S,T) excludes S=T and requires even
# intersection.  Thus all diagonal residual entries are frame-illegal.
def legal_side_edge(S, T):
    return S != T and len(set(S) & set(T)) % 2 == 0

illegal_diagonal = [T for T, j in zip(TRIPLES, J_diag) if j and not legal_side_edge(T, T)]
assert len(illegal_diagonal) == V - H
# Any map supported only on legal side edges has zero diagonal.  An idempotent
# matrix over characteristic zero has trace equal to its rank, so such a map
# cannot be the rank-(v-h) residual J.

N0 = V**3
I0 = 3 * V**2
m = H**3
side_roles = V - H
centre_roles = H
role_count = 2 * N0 + I0 * (side_roles + centre_roles)
padding = 1
while padding < role_count:
    padding <<= 1
centre_saving = 2 * N0 - 2 * I0 * H**2
# Conditional charge if each residual diagonal channel were given a frame:
# the current row-2 -> row-4 -> row-5 boundary loses and regains one prefix
# direction per channel, hence two absolute residual units.
conditional_penalty = 2 * I0 * side_roles
conditional_margin = centre_saving - conditional_penalty
conditional_normalized = Fraction(conditional_margin, m * padding)
max_diagonal_for_positive_margin = (centre_saving - 1) // (2 * I0)
side_role_budget_at_padding = (padding - 2 * N0) // I0 - centre_roles

print({
    "h": H,
    "v": V,
    "selected_centre_triples": H,
    "projection_rank": sum(P_diag),
    "residual_rank": sum(J_diag),
    "residual_trace": sum(J_diag),
    "illegal_diagonal_side_channels": len(illegal_diagonal),
    "original_even_neighbor_count": sum(
        legal_side_edge(S, T) for S in TRIPLES for T in TRIPLES
    ) // V,
    "side_roles_candidate": side_roles,
    "centre_roles": centre_roles,
    "N0": N0,
    "I0": I0,
    "m": m,
    "role_count": role_count,
    "padding": padding,
    "centre_saving": centre_saving,
    "conditional_penalty": conditional_penalty,
    "conditional_margin": conditional_margin,
    "conditional_normalized_margin": str(conditional_normalized),
    "conditional_normalized_margin_float": float(conditional_normalized),
    "max_diagonal_roles_for_positive_margin": max_diagonal_for_positive_margin,
    "side_role_budget_at_padding_2^36": side_role_budget_at_padding,
})
