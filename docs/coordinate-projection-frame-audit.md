# Rank-h coordinate projection: scalar win, frame no-go

A natural follow-up to the centre factorization is to make the centre map a
coordinate projection.  Choose any (h) distinct triples (T_1,ldots,T_h)
and define

\[
  G(x)_i=x_{T_i},\qquad
  (R c)_S=\begin{cases}c_i&S=T_i,\\0&\text{otherwise.}\end{cases}
\]

Then (P=RG) is a rank-(h) projection on the triple space (X).  The
complement (J=I-P) is also a projection, with rank (v-h): it is the
identity on every unselected triple.  Thus the eight-row scalar identity can
be written with (h) centre coordinates and only (v-h) residual side
coordinates, instead of the (v\,d_{\rm nbr}) ordered-neighbour roles.

The exact h=24 arithmetic is reproducible with
[`scripts/coordinate_projection_frame_audit.py`](../scripts/coordinate_projection_frame_audit.py):

| quantity | value |
|---|---:|
| (v=\binom{24}{3}) | 2,024 |
| centre rank | 24 |
| residual rank (v-h) | 2,000 |
| candidate side roles/invocation | 2,000 |
| centre roles/invocation | 24 |
| (N_0=v^3) | 8,291,469,824 |
| (I_0=3v^2) | 12,289,728 |
| scalar role count (2N_0+I_0((v-h)+h)) | 41,457,349,120 |
| next power-of-two padding | (2^{36}=68,719,476,736) |

This apparent scalar reduction is incompatible with the published frame labels.
Every residual coordinate has a diagonal matrix coefficient (J_{T,T}=1).  A
published side role is indexed by a **distinct** ordered pair ((S,T)) with
even (|S\cap T|); in particular it has (J_{S,S}=0).  Therefore every
frame-compatible side map has zero diagonal.  Over the complex scalar field,
an idempotent matrix has `trace = rank`.  A side map with zero diagonal has
trace zero, so it cannot be the rank-((v-h)=2000) projection required here.
For the explicit coordinate candidate, all 2,000 residual channels are
therefore frame-illegal.  This is an algebraic obstruction, independent of
which 24 triples are selected.

For scale, if one hypothetically added a legal frame for each diagonal channel,
the current row-2/row-5 boundary would charge two absolute residual units per
channel.  The conditional charge is

\[
  2I_0(v-h)=49,158,912,000,
\]

against the centre saving
(2N_0-2I_0h^2=2,425,172,992).  The resulting conditional margin is
\(-46,733,739,008), or

\[
 -\frac{45,638,417}{927,712,935,936}
 \approx -4.91945\times 10^{-5}
\]

when normalized by (24^3 2^{36}).  This latter number is only a boundary
cost audit; it does not rescue the candidate, because the required diagonal
side channels do not exist in the current frame schedule.  To make a
rank-(h) projection useful, the circuit must change the side boundary to
permit diagonal source/target channels (or move the residual into a new
centre-like bank); that is a new frame construction, not a parameter tweak.

Run:

```bash
python3 scripts/coordinate_projection_frame_audit.py
```
