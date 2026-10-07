"""Frame audit for the scalar side-moment factorization.

The scalar identity is
sideNoDiag(S,x)=(q-sum_{i in S} a_i)/2 and
sideAction=sideNoDiag+x_S.  The moment wires q,a_i can be folded into the
existing centre bank, but the final x_S term needs a direct diagonal channel.

A direct diagonal bank has one role per source/target triple and is touched
by the row-2 source frame and row-4 centre target frame.  Its source line
must drop a prefix direction before the row-4 B⊗D gate and later return to
the full X frame: two residual units per direct role/invocation.  The
resulting 2*I0*v penalty exceeds the h=24 centre saving.

This is conditional on the existing eight-row boundaries, not a universal
lower bound.
"""
from fractions import Fraction
from math import comb

def audit_h24():
    h=24; v=comb(h,3); N0=v**3; I0=3*v*v; m=h**3
    # q+a_i folded into h existing centre roles; one direct diagonal role/T.
    W=2*N0+I0*(v+h)
    pad=1
    while pad<W: pad<<=1
    delta=2*N0-2*I0*h*h
    penalty=2*I0*v
    return {
      "h":h,"v":v,"N0":N0,"I0":I0,"m":m,
      "direct_roles_per_invocation":v,
      "role_count":W,"padding":pad,
      "centre_delta":delta,"direct_diagonal_penalty":penalty,
      "effective_delta":delta-penalty,
      "normalized_margin":str(Fraction(delta-penalty,m*pad)),
      "normalized_margin_float":float(Fraction(delta-penalty,m*pad)),
    }

if __name__=="__main__":
    print(audit_h24())

