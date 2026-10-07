"""Exact scalar/frame audit for a pair-complement side factorization.

For a target triple S and source triple T, let r=|S∩T|.  For every pair F
define A_F=sum_{T superset F} x_T and B_F=sum_{T disjoint F} x_T.
The target reads only A_F with F subset S and B_F with F disjoint S.
Their coefficient counts are C(r,2) and C(h-6+r,2), respectively.  Their
difference is affine in r, giving the diagonal-free side coefficient
(1-r)/2 after adding the global moment.

This is a scalar identity plus a labelled-span audit.  It is not a complete
replacement network: the eight-row schedule and all gate maps still need a
formal construction.
"""
from itertools import combinations
from fractions import Fraction
from math import comb

def rank_gf2(rows):
    piv = {}
    for x in rows:
        while x:
            p = x.bit_length() - 1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p] = x
                break
    return len(piv)

def indicator(S):
    z = 0
    for i in S:
        z |= 1 << i
    return z

def span_rank(vectors):
    return rank_gf2([indicator(T) if not isinstance(T, int) else T
                     for T in vectors])

def orthogonal_basis(v, h):
    """A deterministic basis for v-perp when v is a weight-three indicator."""
    supp = [i for i in range(h) if (v >> i) & 1]
    if len(supp) < 2:
        # Not used by the audit, but keep the helper total.
        return [1 << i for i in range(h) if not ((v >> i) & 1)]
    p, q = supp[0], supp[1]
    rows = [1 << i for i in range(h) if i not in supp]
    rows.append((1 << p) | (1 << q))
    for r in supp[2:]:
        rows.append((1 << p) | (1 << r))
    return rows

def pair_span(h, F, *, disjoint=False):
    Ts = list(combinations(range(h), 3))
    if disjoint:
        ts = [T for T in Ts if set(T).isdisjoint(F)]
    else:
        ts = [T for T in Ts if set(F).issubset(T)]
    return rank_gf2([indicator(T) for T in ts]), ts

def target_span(h, F, *, disjoint=False):
    return pair_span(h, F, disjoint=disjoint)

def check_scalar(h):
    assert h >= 7
    c = h - 6
    for r in range(4):
        m2 = comb(r, 2)
        mc = comb(c + r, 2)
        lhs = Fraction(m2 - mc, 2*c) + Fraction(1, 2) + Fraction(c - 1, 4)
        assert lhs == Fraction(1-r, 2), (h, r, lhs)
    return c

def check_spans(h):
    pair_ranks = set()
    disjoint_ranks = set()
    target_orth_join_ranks = set()
    for F in combinations(range(h), 2):
        r, src = pair_span(h, F)
        rd, srcd = pair_span(h, F, disjoint=True)
        pair_ranks.add(r)
        disjoint_ranks.add(rd)
        # The row-5 labels contain t_S^perp for every target in the same
        # class.  Their join should be the full D; verify by collecting
        # explicit orthogonal hyperplane generators.
        for disjoint, targets in [(False, src), (True, srcd)]:
            vectors = []
            for T in targets:
                t = indicator(T)
                vectors.extend(orthogonal_basis(t, h))
            target_orth_join_ranks.add(rank_gf2(vectors))
    assert pair_ranks == {h - 2}, pair_ranks
    assert disjoint_ranks == {h - 2}, disjoint_ranks
    assert target_orth_join_ranks == {h}, target_orth_join_ranks

def stage_role_cost(h, rankL, e):
    """Residual dimensions for source->row0->row2->row5->row7.

    B has dimension e-1 and P is a line.  Row0 uses B⊗L; row2 uses
    B⊗D ⊥ P⊗L; row5 joins all target complements and uses E⊗D; row7
    is E⊗D.  The four nonnegative changes telescope to e*h.
    """
    b = e - 1
    source_to_row0 = b * rankL
    row0_to_row2 = b * (h-rankL) + rankL
    row2_to_row5 = h - rankL
    row5_to_row7 = 0
    pieces = (source_to_row0, row0_to_row2, row2_to_row5, row5_to_row7)
    assert sum(pieces) == e*h, (h, rankL, e, pieces)
    return pieces

def check_frame_cost(h):
    for j in (1, 2, 3):
        e = h ** (j-1)
        assert stage_role_cost(h, h-2, e) == ((e-1)*(h-2),
            (e-1)*2 + h-2, 2, 0)
    # Compare with the original pair-specific route: same total e*h.
    for j in (1, 2, 3):
        e = h ** (j-1)
        b = e-1
        original = (b, b*(h-1)+1, h-2, 1)
        assert sum(original) == e*h

def joint_gate_join_rank(h, anchor, *, disjoint):
    """Join of aggregate spans touched by one target/source gate.

    A gate for a target (or source) touches every pair aggregate in one of
    the two relevant classes.  The active labels of those aggregates are the
    spans returned by ``pair_span``.  This rank is the frame dimension forced
    by one common gate before any new scheduling or copying is introduced.
    """
    anchor_set = set(anchor)
    pairs = [
        F for F in combinations(range(h), 2)
        if (set(F).isdisjoint(anchor_set) if disjoint else set(F).issubset(anchor_set))
    ]
    rows = []
    for F in pairs:
        _, labels = pair_span(h, F, disjoint=disjoint)
        rows.extend(indicator(T) for T in labels)
    return rank_gf2(rows)


def check_joint_gate_joins(h):
    """Check the common-gate join obstruction at ``h=24``.

    Both three-pair A families and 210-pair B families already join to the
    full active factor.  The same holds for source-side row-2 families.  This
    does not rule out a redesigned schedule; it only rules out treating all
    aggregate touches as one rank-``h-2`` common gate.
    """
    target = (0, 1, 2)
    source = (0, 1, 3)
    joins = {
        "row0_A_target": joint_gate_join_rank(h, target, disjoint=False),
        "row0_B_target": joint_gate_join_rank(h, target, disjoint=True),
        "row2_A_source": joint_gate_join_rank(h, source, disjoint=False),
        "row2_B_source": joint_gate_join_rank(h, source, disjoint=True),
    }
    assert joins == {name: h for name in joins}, joins
    return joins

def h24_arithmetic():
    h = 24
    v = comb(h, 3)
    N0 = v**3
    I0 = 3*v**2
    m = h**3
    pair_count = comb(h, 2)
    d_nbr = comb(h-3, 3) + 3*(h-3)
    W_original = 2*N0 + I0*(v*d_nbr + h)
    W_candidate = 2*N0 + I0*(2*pair_count + h)
    pad = 1
    while pad < W_candidate:
        pad *= 2
    delta = 2*N0 - 2*I0*h*h
    return {
        "h": h, "v": v, "N0": N0, "I0": I0, "m": m,
        "pair_count": pair_count, "dNbr": d_nbr,
        "W_original": W_original, "W_pair_complement": W_candidate,
        "candidate_padding": pad,
        "candidate_delta": delta,
        "candidate_epsilon": Fraction(delta, m*pad),
        "candidate_epsilon_float": float(Fraction(delta, m*pad)),
        "candidate_width_reduction": Fraction(W_original, W_candidate),
        "original_side_roles_per_invocation": v*d_nbr,
        "candidate_side_roles_per_invocation": 2*pair_count,
        "joint_gate_join_ranks": check_joint_gate_joins(h),
    }

if __name__ == "__main__":
    for h in (7, 8, 24):
        check_scalar(h)
        check_spans(h)
        check_frame_cost(h)
    # The full-dimensional join is only asserted for the h=24 audit below;
    # keep the small scalar/span checks above reusable for other h.
    print(h24_arithmetic())
