# Phase profiles under binary address changes

`AddressPhaseConjugation.lean` separates binary label transport from complex
data transport.  For any complex diagonal phase profile `q` and any binary
linear equivalence `e`, the induced monomial address matrix satisfies

```text
P_e diag(q) P_e⁻¹ = diag(q ∘ e⁻¹).
```

An invariant profile commutes with `P_e`; a framed phase
`J diag(q) J` has the corresponding conjugacy theorem when the two required
commutation relations with the common frame `J` are supplied explicitly.  The
selective centre's `unitCoordinateEquiv` is included as a concrete instance of
the address relabelling formula.

The theorem deliberately leaves the Walsh matrix, quadratic phase profile, and
global propagation as separate obligations.  It therefore records the exact
semantic bridge without pretending that a binary transvection is itself one
charged complex shear.
