# Target-routed dense frame audit

`DenseTargetRoutedFrameAudit.lean` packages the strongest local consequence of
the even-width two-label cover.  For a target triple (S), `targetRoute` is
the identity on the unit block and the exact binary `denseSwap` on the dense
block.  The certificate proves that it maps the anchored unit label to the
unique label in `targetBoundary S`; its fibrewise address lift is a monomial
permutation.  This is the precise local premise needed before charging a
target-indexed address change as free.

Under that explicit free-routing premise, the three prefix switches in the
serialized block ledger disappear.  The route charge is therefore zero,
instead of `1202`, and the exact H24 margin is

```text
2,425,172,992
```

with normalized finite saving

```text
2368333 / 474989023199232 ≈ 4.986079434106445 × 10⁻⁹.
```

The previous switch ledger is

```text
1212585895 / 243194379878006784 ≈ 4.986076962832231 × 10⁻⁹.
```

If the inherited recurrence multiplier is `13824 · (1 − ε)`, these values
correspond numerically to exponent gaps approximately

```text
5.229698963270910 × 10⁻¹⁰  (zero-switch route)
5.229696371250386 × 10⁻¹⁰  (three-switch route).
```

Thus the local improvement is only about (2.59	imes10^{-16}) in the
exponent and remains below (10^{-9}).  These decimals are explanatory
evaluations; the Lean theorem checks the exact rational finite ledger.

The same file proves a concrete obstruction to dropping the phase transport:
`denseSwap` moves an explicit address, so a diagonal profile that separates
that address is relabelled nontrivially.  A free monomial route therefore still
needs either an invariance proof for the actual `q_U` profile or an explicit
phase-conjugation schedule.  The result is conditional and local; it is not a
complex-circuit construction, a lower bound, or an all-length DFT theorem.

Validate the certificate from the Lean directory with:

```bash
lake env lean -DautoImplicit=false \
  OAI/Computability/FourierCircuit/DenseTargetRoutedFrameAudit.lean
```
