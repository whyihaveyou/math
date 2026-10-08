# Binary frame to one-gate complex transport: a concrete no-go

`BinaryComplexFrameMap.lean` defines the pointwise support encoding
`bitVectorToComplex : (ι → ZMod 2) → (ι → ℂ)` and records the characteristic
zero obstruction to any additive map from `ZMod 2` into `ℂ`.  It also proves the
only safe local identity currently available: if a binary label and a
coordinate vector have disjoint support, their binary sum is sent to ordinary
complex addition.

`BinaryComplexFrameMap.lean` also proves the positive restricted identity
`bitVectorToComplex_binarySingleAdd`: a single binary row update agrees with a
coefficient-one `Gate.add` when the two input bits are disjoint.  The same file
contains a generic `no_fin2_shear_support_transport` theorem ruling out any
single complex shear as a global realization of the smallest binary swap.

`BinaryComplexFrameGateNoGo.lean` makes the remaining gap executable at the
smallest dimension.  On `Fin 2`, the isotropic binary direction
`u = e₀ + e₁` gives the binary transvection that swaps `e₀` and `e₁`.  The
oriented unit complex shear with target `0`, source `1`, coefficient `1`
(`Gate.add`) fixes the complex support vector of `e₀`.  Lean proves

```text
¬ FrameToComplexShearPremise (e₀ + e₁) unitAddShear
```

by evaluating the proposed transport identity on `e₀` at coordinate `1`.
Thus the one-gate accounting certificate cannot be paired with the binary
transvection by simply applying the support encoding globally, even in the
smallest nontrivial example.

This is route-specific.  It does not lower-bound arbitrary complex circuits:
wire permutations are free in the `LinearDAG` interface, and multiple shears
may realize a swap.  The precise open condition for a positive one-gate frame
ledger is now explicit: provide a different non-additive frame-to-coordinate
encoding and prove its `FrameToComplexShearPremise`, or replace the binary
transvection by a complex operation whose action is actually realized by the
chosen `Gate.add` and whose frame transport is scheduled globally.

Build with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.BinaryComplexFrameGateNoGo
```
