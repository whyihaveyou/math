"""Arithmetic/frame audit for a source-indexed side bank.

A source-indexed bank has one auxiliary per source triple T rather than one
per ordered neighboring pair (S,T).  Its row-2 source update is cheap, but
each bank wire is read by all even-neighbor targets S.  The target labels
t_S^perp for these S have full join (the target indicators span t_T^perp,
whose orthogonals join to D).  Under the existing row-5 boundary, a common
full frame makes every target y_S rise and return across one prefix direction:
the same 2*I0*v penalty as a target aggregate bank.

The script checks ranks at h=24 and exact role/padding arithmetic.  This is a
conditional audit for the existing eight-row boundaries, not a universal
lower bound.
"""
from itertools import combinations
from fractions import Fraction
from math import comb

def rank(rows):
    basis={}
    for x in rows:
        while x:
            p=x.bit_length()-1
            if p in basis: x^=basis[p]
            else: basis[p]=x; break
    return len(basis)

def ind(S):
    z=0
    for i in S:z|=1<<i
    return z

def perp_basis(t,h):
    supp=[i for i in range(h) if (t>>i)&1]
    p,q=supp[:2]
    rows=[1<<i for i in range(h) if i not in supp]
    rows += [(1<<p)|(1<<q)]
    rows += [(1<<p)|(1<<supp[2])]
    return rows

def audit_h24():
    h=24; T=(0,1,2); tv=ind(T)
    targets=[S for S in combinations(range(h),3)
             if (len(set(S)&set(T))%2)==0 and tuple(S)!=T]
    assert len(targets)==1393
    target_rank=rank([ind(S) for S in targets])
    perp_join=rank([z for S in targets for z in perp_basis(ind(S),h)])
    assert target_rank==h-1 and perp_join==h
    v=comb(h,3); I0=3*v*v; N0=v**3; m=h**3
    role_count=2*N0+I0*(v+h)
    pad=1
    while pad<role_count:pad<<=1
    delta=2*N0-2*I0*h*h
    penalty=2*I0*v
    return {
      "h":h,"source":T,"even_neighbor_targets":len(targets),
      "target_indicator_span_rank":target_rank,
      "row5_complement_join_rank":perp_join,
      "v":v,"N0":N0,"I0":I0,"m":m,
      "role_count":role_count,"padding":pad,"centre_delta":delta,
      "conditional_penalty":penalty,
      "effective_delta":delta-penalty,
      "normalized_margin":str(Fraction(delta-penalty,m*pad)),
      "normalized_margin_float":float(Fraction(delta-penalty,m*pad)),
    }

if __name__=="__main__":
    print(audit_h24())

