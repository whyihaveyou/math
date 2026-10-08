# Four singleton labels cover a target boundary

[`TargetLabelCover.lean`](../lean/OAI/Computability/FourierCircuit/TargetLabelCover.lean)
formalizes a small target-routing witness.  For `h ≥ 4` it embeds `Fin 4` in
`Fin h` using `Fin.castLEEmb`, and assigns each of the four coordinates its
singleton label `e_i`.  If `S` is any triple, at least one embedded coordinate
is outside `S`, because the image has cardinality four while `S` has
cardinality three.  The corresponding singleton has

```text
dotForm (indicator S) e_i = 0,
```

so it belongs to the target boundary
`((ZMod 2) ∙ indicator S)ᗮ`.

The module records unit norm and pairwise orthogonality of the four labels,
their injectivity, and packages them as
`FourFrameTargetRoutingWitness`.  Its `target_hit` field is the existential
legal label for the target line.  This is a label-level cover only: it does not
form source aggregates, establish scalar/gate commutation, realize gates, or
provide a global schedule or a cost bound.  In particular, it cannot by itself
turn the parity-split candidate into an improved DFT exponent.

The checked theorem is:

```lean
∃ i : Fin 4, singletonLabel hh i ∈ targetBoundary S
```

for every `hh : 4 ≤ h` and `S : Triple h`; the companion structure exposes the
same statement together with the four explicit frame labels.  The companion
[`SingletonCoverMinimality.lean`](../lean/OAI/Computability/FourierCircuit/SingletonCoverMinimality.lean)
formalizes that four is minimal when the allowed labels are singleton
coordinates: any cover of all triples has cardinality at least four, and the
canonical `Fin 4` image has exactly four.
