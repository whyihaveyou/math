# Pair/complement all-length attachment interface

`PairComplementAllLengthBridge.lean` attaches the exact h=24 scalar
pair/complement invocation to a frame at every finite product-tower prefix.
For a `FrameTowerSchedule 24`, it proves:

* source and target full-address labels are unit and orthogonal;
* the source label at depth `k` is carried to the next prefix by the
  fibrewise `tensorLift`;
* forward, inverse, and exchange invocations restore the scalar state while
  preserving their attached frame label.

The bridge is deliberately an interface rather than a circuit theorem.  It
does not prove that `tensorLift` is a legal complex gate sequence, that the
pair-bank map commutes with those gates, or that the finite stages fit one
global DAG with the required cost.  Those premises remain open.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.PairComplementAllLengthBridge
```
