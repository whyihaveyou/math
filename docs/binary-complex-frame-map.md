# Binary-frame / complex-coordinate boundary

`BinaryTransvection` and the frame audits use vectors over `ZMod 2`.  The
scalar circuit model in `ComplexShearGateBridge` uses vectors over `ℂ`.  These
are different algebraic interfaces.

`BinaryComplexFrameMap.lean` records two exact local facts:

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

Consequently, the current parameter ledgers must not charge a binary
transvection as a complex `Gate.add` until this premise is proved for the
chosen encoding and schedule.  The certificate is local and does not claim a
global circuit or an all-length DFT theorem.
