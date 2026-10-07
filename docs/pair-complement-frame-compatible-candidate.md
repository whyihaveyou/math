# Pair/complement frame-compatible candidate (conditional)

`PairComplementFrameCompatibleCandidate.lean` joins the local rank facts and
the aggregate-wise boundary ledger for the pair/complement side-bank proposal.
It records a concrete conditional candidate; it does not prove a physical
complex-gate schedule.

For every fixed pair (F\subset [24]), both support families have rank 22
over (mathbf F_2):

* (A_F) is spanned by indicators of triples containing (F);
* (B_F) is spanned by indicators of triples disjoint from (F).

The first equality is the `pairSpan_finrank` certificate, and the second is
the disjoint-triple span theorem.  Thus both banks meet the rank premise
(r=h-2) of the aggregate-wise four-edge ledger.  Under that ledger, one
aggregate at prefix size (e) has directional charge (e h).  The three
prefix sizes (1, h, h^2) therefore cost

\[
 h(1+h+h^2)=14{,}424
\]

per bank aggregate, or (2\binom{24}{2}\cdot14{,}424=7{,}962{,}048) for the
two banks.

The scalar role count is

\[
W=23{,}661{,}822{,}976,
\qquad 2^{34}<W\le 2^{35}=34{,}359{,}738{,}368.
\]

The side roles per invocation drop from

\[
\binom{24}{3}\,d_{\rm nbr}=2{,}819{,}432
\]

to (2\binom{24}{2}=552), a reduction of (2{,}818{,}880), greater than a
factor of 1,000.  Keeping the existing centre directional saving, the
conditional normalized value is

\[
\frac{2{,}368{,}333}{463{,}856{,}467{,}968}
 \approx 5.1057453\times10^{-6},
\]

which is formally greater than both (10^{-9}) and (10^{-6}).

The word **conditional** is essential.  The Lean file proves the binary span
ranks and integer ledger only.  It does not yet prove that the B-bank can be
transported through every row-2/row-5 gate with the displayed nested labels,
that a single complex gate realizes the aggregate read/write maps, or that
the arbitrary-auxiliary restoration and all-length recursion preserve these
frames.  A successful implementation of those premises would turn this
arithmetic candidate into a circuit result; until then the (5.1057\times
10^{-6}) number is a research target, not a proved exponent improvement.

Reproduce the Lean check with:

```bash
cd lean
lake env lean OAI/Computability/FourierCircuit/PairComplementFrameCompatibleCandidate.lean
```
