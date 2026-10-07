# Termwise oblique projection support audit (conditional)

Suppose a rank-(h) centre projection (P=RG) is written as (h)
rank-one terms (u_i v_i^\top), and impose the strong premise that each term
is individually frame-compatible: whenever both (u_i(S)) and (v_i(T)
are nonzero, the two triples (S,T) are distinct with even intersection (a
diagonal pair is allowed only when a full row-2 label is paid).  This forbids
cancellation between dense terms on the odd-intersection positions.

The diagonal support of one term is a family of 3-sets with pairwise even
intersection.  Their indicator vectors have Gram matrix equal to the identity
over \(\mathbb F_2\), so they are linearly independent and there are at most
(h) of them.  Therefore, at (h=24), at most (24^2=576) diagonal entries of
(P) can be nonzero.  The residual (Q=I-P) then has at least
(2024-576=1448) diagonal channels.

Charging the modified row-2 frame two directions per diagonal channel gives

\[
  2I_0(1448)=35{,}591{,}052{,}288,
\]

which exceeds the centre saving
(2N_0-2I_0h^2=2{,}425{,}172{,}992).  The conditional margin is
\(-33{,}165{,}879{,}296), normalized by (24^3 2^{36}) as

\[
 -\frac{16{,}194{,}277}{463{,}856{,}467{,}968}
 \approx -3.49123\times 10^{-5}.
\]

Thus no positive margin is possible under this termwise support premise,
even before charging off-diagonal side roles.  A construction that beats this
bound must use cancellations between rank-one terms on forbidden positions or
a different non-termwise frame transport; it needs a separate exact support
and label certificate.

Run:

```bash
python3 scripts/termwise_projection_support_audit.py
```
