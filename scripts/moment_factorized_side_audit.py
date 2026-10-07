"""Audit the global/incidence (moment) side factorization at h=24.

The existing ``CenterMap.compressedG``/``compressedR`` maps use

    q = sum_T x_T,   a_i = sum_{T contains i} x_T,
    c_i = a_i - q/3,

and read ``(1/2) sum_{i in S} c_i``.  Its coefficient on x_T is
``(|S intersect T|-1)/2``.  The diagonal-free side correction is the
negative of this coefficient plus a direct x_S term.

This script checks the binary support spans relevant to the existing row-5
frame and gives a concrete scalar-gate count for a naive moment realization.
It is conditional: the current CompressedInvocation J-map receives only the
side bank, so the direct x_S term needs either an interface extension or one
source wire per target.  No universal lower bound is claimed.
"""
from itertools import combinations
from fractions import Fraction
from math import comb


def rank_gf2(rows):
    basis = {}
    for x in rows:
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def indicator(S):
    z = 0
    for i in S:
        z |= 1 << i
    return z


def perp_basis(t, h):
    """Explicit binary basis for the hyperplane t^perp, |t|=3."""
    supp = [i for i in range(h) if (t >> i) & 1]
    p, q, r = supp
    rows = [1 << i for i in range(h) if i not in supp]
    rows += [(1 << p) | (1 << q), (1 << p) | (1 << r)]
    return rows


def support_rank(h, predicate):
    triples = list(combinations(range(h), 3))
    return rank_gf2([indicator(T) for T in triples if predicate(T)])


def frame_join_audit(h=24):
    triples = list(combinations(range(h), 3))
    all_rank = support_rank(h, lambda T: True)
    incidence_ranks = [support_rank(h, lambda T, i=i: i in T)
                       for i in range(h)]
    fixed_target = (0, 1, 2)
    incidence_target_join = rank_gf2(
        [indicator(T) for T in triples
         if any(i in T for i in fixed_target)])
    # A global q wire is used by every target.  Its source labels already
    # span D, so the common row-5 frame is full before incidence wires join.
    q_row5_join = rank_gf2(
        [z for S in triples for z in perp_basis(indicator(S), h)])
    # If q is reconstructed from centered c_i, every c_i has nonzero support
    # on all triples (coefficients 2/3 and -1/3), hence the same label span.
    centered_wire_rank = all_rank
    return {
        "h": h,
        "triple_count": len(triples),
        "q_source_span_rank": all_rank,
        "incidence_source_span_rank_min": min(incidence_ranks),
        "incidence_source_span_rank_max": max(incidence_ranks),
        "three_incidence_target_join_rank": incidence_target_join,
        "row5_target_complement_join_rank": q_row5_join,
        "centered_wire_source_span_rank": centered_wire_rank,
    }


def scalar_gate_count(h=24):
    v = comb(h, 3)
    # q has v summands.  Each a_i has C(h-1,2) summands.
    q_adds = v - 1
    incidence_terms = comb(h - 1, 2)
    incidence_adds = h * (incidence_terms - 1)
    # One shared q/3 scale and h subtractions form c_i.
    center_shift_gates = 1 + h
    # Each target reads three c_i: two adds and one scale by -1/2.  The
    # diagonal correction reads the original x_S once.  The final y update is
    # listed separately because it is a row gate in the invocation.
    target_count = v
    moment_readout_gates = target_count * 3
    direct_diagonal_adds = target_count
    y_update_adds = target_count
    prepared = q_adds + incidence_adds + center_shift_gates
    return {
        "h": h,
        "v": v,
        "q_adds": q_adds,
        "incidence_terms_per_i": incidence_terms,
        "incidence_adds": incidence_adds,
        "center_shift_gates": center_shift_gates,
        "moment_readout_gates": moment_readout_gates,
        "direct_diagonal_adds": direct_diagonal_adds,
        "y_update_adds": y_update_adds,
        "aggregate_and_readout_gates": prepared + moment_readout_gates + direct_diagonal_adds,
        "aggregate_readout_y_update_gates": prepared + moment_readout_gates + direct_diagonal_adds + y_update_adds,
    }


def width_arithmetic(h=24):
    v = comb(h, 3)
    n0 = v ** 3
    i0 = 3 * v ** 2
    m = h ** 3
    # h centered moments plus an explicit q side wire: (h+1) side roles.
    # The centre bank already has h roles, hence 2h+1 total roles per
    # invocation in the same width ledger as the pair audits.
    side_roles = h + 1
    total_roles = side_roles + h
    width = 2 * n0 + i0 * total_roles
    pad = 1
    while pad < width:
        pad <<= 1
    centre_delta = 2 * n0 - 2 * i0 * h * h
    common_full_frame_penalty = 2 * i0 * v
    return {
        "h": h,
        "side_roles": side_roles,
        "total_roles_per_invocation": total_roles,
        "width": width,
        "padding": pad,
        "centre_delta": centre_delta,
        "conditional_full_frame_penalty": common_full_frame_penalty,
        "conditional_effective_delta": centre_delta - common_full_frame_penalty,
        "conditional_normalized_margin": str(Fraction(centre_delta - common_full_frame_penalty, m * pad)),
        "conditional_normalized_margin_float": float(Fraction(centre_delta - common_full_frame_penalty, m * pad)),
    }


if __name__ == "__main__":
    print({"frame": frame_join_audit(), "gates": scalar_gate_count(), "width": width_arithmetic()})
