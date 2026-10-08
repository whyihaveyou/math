# Binary-frame / complex-coordinate boundary

`BinaryTransvection` and the frame audits use vectors over `ZMod 2`.  The
scalar circuit model in `ComplexShearGateBridge` uses vectors over `ℂ`.  These
are different algebraic interfaces.

`BinaryComplexFrameMap.lean` records two exact local facts:

The support-map model in this file is a deliberately strong proposed
encoding, not the semantic model used by the paper.  In the paper, binary
labels index complex array addresses and define the operators `Φ_U`; they are
not embedded as complex data vectors.  The corresponding free address-change
bridge is formalized in `BinaryAddressPermutation.lean`.

* every additive map `ZMod 2 →+ K` into a characteristic-zero field is zero;
  in particular, there is no nonzero additive or linear embedding of a binary
  frame label into a complex coordinate;
* the 0/1 support map does preserve a binary sum at coordinates where the two
  supports are disjoint.  For `t w = 0`, it sends `t + coordinate w` to the
  ordinary complex vector sum of the support of `t` and the complex coordinate
  at `w`.

The file also defines `FrameToComplexShearPremise`.  It is an explicit open
premise for a future semantic bridge: a proposed complex shear must transport
all encoded binary transvection inputs.  The premise is not inferred from the
binary algebra.  Once a complex shear is supplied, `ComplexShearGateBridge`
gives its exact scalar-gate realization (`Gate.add` for coefficient `1`, two
scalar gates for an arbitrary coefficient).

The new unit-shear checks make the boundary concrete.  The restricted update
`binarySingleAdd i j` agrees with the coefficient-one complex shear on inputs
where the destination and source bits are not both `1`; this is the exact
local positive case behind a `Gate.add`.  The smallest nonzero isotropic
transvection, with binary direction `(1,1)` on `Fin 2`, sends `e₀` to `e₁`.
`no_fin2_shear_support_transport` proves that no single complex shear can
match its support-map semantics: the binary map clears coordinate `0`, while
every complex shear leaves that coordinate equal to its input when it is a
source, or adds a zero source when it is the destination.  This is a local
counterexample to charging an arbitrary binary transvection as one `Gate.add`.

Consequently, the current parameter ledgers must not charge a binary
transvection as a complex `Gate.add` until this premise is proved for the
chosen encoding and schedule.  The certificate is local and does not claim a
global circuit or an all-length DFT theorem.
