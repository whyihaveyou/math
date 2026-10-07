"""Joint-gate obstruction for the global pair/complement candidate.

The scalar identity in pair_complement_side_audit.py uses all triples in each
pair aggregate.  For a fixed target S, a row-5 gate touches y_S and every
aggregate used by S.  The source span L_F of each all-triple pair aggregate
is not contained in t_S^perp (A_F contains T=S when F subset S; B_F contains
both r=0 and r=1 sources when F disjoint S).  Therefore the common row-5
frame must include P⊗D, while the stage boundary for y_S is
(B⊗D) ⊥ (P⊗t_S^perp).  Returning to that boundary loses one P-direction,
and the absolute residual cost charges two units per target invocation.

This is a conditional obstruction for the existing eight-row boundaries.  It
does not lower-bound arbitrary redesigned networks.
"""
from itertools import combinations
from fractions import Fraction
from math import comb

def rank(rows):
    b = {}
    for x in rows:
        while x:
            p = x.bit_length()-1
            if p in b: x ^= b[p]
            else: b[p] = x; break
    return len(b)

def ind(S):
    z=0
    for i in S: z |= 1<<i
    return z

def pair_support(h,F,complement=False):
    return [ind(T) for T in combinations(range(h),3)
            if (set(T).isdisjoint(F) if complement else set(F).issubset(T))]

def target_intersection(F,S):
    return len(set(F)&set(S))

def audit_h24():
    h=24; S=(0,1,2)
    classes = {
      "A": [F for F in combinations(S,2)],
      "B": [F for F in combinations(range(h),2) if set(F).isdisjoint(S)],
    }
    pair_ranks = {k: {rank(pair_support(h,F, k=="B")) for F in Fs}
                  for k,Fs in classes.items()}
    joins = {k: rank([z for F in Fs for z in pair_support(h,F,k=="B")])
             for k,Fs in classes.items()}
    assert pair_ranks == {"A": {h-2}, "B": {h-2}}
    assert joins == {"A": h, "B": h}
    # For every aggregate used at S, its source span includes an odd-overlap
    # label with t_S, so it is not contained in t_S-perp.
    bad = []
    svec=ind(S)
    for k,Fs in classes.items():
        for F in Fs:
            rows=pair_support(h,F,k=="B")
            assert any((bin(z&svec).count("1")%2) == 1 for z in rows)
            bad.append((k,F))
    assert len(bad) == 3+comb(h-3,2)
    v=comb(h,3); I0=3*v*v; N0=v**3; m=h**3
    delta=2*N0-2*I0*h*h
    penalty=2*I0*v
    return {
      "h":h, "target":S,
      "aggregate_counts":{"A":len(classes["A"]),"B":len(classes["B"]),
                          "total":len(bad)},
      "source_span_rank":{"A":h-2,"B":h-2},
      "joint_target_gate_join_rank":joins,
      "odd_overlap_aggregate_count":len(bad),
      "boundary_loss_per_target":1,
      "directional_penalty":penalty,
      "centre_delta":delta,
      "effective_delta":delta-penalty,
      "effective_normalized":str(Fraction(delta-penalty,m*2**35)),
      "effective_normalized_float":float(Fraction(delta-penalty,m*2**35)),
    }

if __name__=="__main__":
    print(audit_h24())

