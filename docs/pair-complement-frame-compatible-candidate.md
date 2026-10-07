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

## Active-label permutation transport

`PairComplementFramePermutation.lean` adds the missing label-space transport
lemma for the B-bank.  For an equivalence `e : Fin h ≃ Fin h`, the linear
reindexing `x ↦ x ∘ e.symm` maps `awaySubmodule F` exactly onto
`awaySubmodule (F.image e)`.  Since the disjoint-triple span equals the away
submodule for a pair and `h ≥ 6`, it follows that

```text
map (activeReindex e) (disjointTripleSpan F)
  = disjointTripleSpan (F.image e).
```

At `h = 24` the transported span still has rank 22.  This is a concrete
premise for reusing a B-bank after an active-label permutation; it does not
claim that the permutation is a legal complex gate or supply the missing
physical all-prefix schedule.

## Tensor-side frame bridge

`PairComplementFramePermutationBridge.lean` lifts the active-label equivalence to
`ι × Fin h` addresses through `CenterBoundaryTensorLift`.  For a fixed prefix
`p`, the inserted disjoint B-bank is defined as the range of the insertion map
restricted to `disjointTripleSpan F`.  The theorem
`lifted_bank_map_eq` proves that this submodule is carried exactly to the
inserted bank for `F.image e`; the h=24 specialization preserves the rank-22
B-bank certificate.  This supplies a concrete tensor-side frame-transport
premise for the conditional pair/complement ledger.  It still does not assert
complex-gate legality, scalar/gate commutation, or a global all-prefix DAG.
