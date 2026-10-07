# Complex shear to scalar-gate bridge

The frame audit uses a matrix-level primitive
\[
  x\longmapsto x+c\,x_j e_i,
\]
represented by `Shear` / `Matrix.TransvectionStruct`.  The executable circuit
model in `Core.lean` charges `Gate.scale`, `Gate.add`, and `Gate.sub` separately.
`ComplexShearGateBridge.lean` supplies the exact local interface between these
layers.

For every finite `n` and every complex shear `s` on `Fin n`,
`twoGateShear s : LinearDAG n n` has size exactly `2` and computes
`s.toMatrix.mulVec`.  Its first scalar gate computes `s.c * x s.j`; its second
adds that value to `x s.i`; the other outputs are read-only input wires.  The
proof is `twoGateShear_eval`, followed by `Shear.act_eq_mulVec`.  The packaged
`ScalarShearWitness` exposes the same result with a size bound suitable for a
later schedule theorem.

This is a local semantic bridge only.  The binary frame labels live over
`ZMod 2`, while complex gates act on `ℂ`-valued wires.  No map from a binary
label transformation (`unitCoordinateEquiv`) to a complex gate is defined
here, and no frame-preservation or global scheduling theorem is assumed.
Therefore the existing six-phase ledger remains conditional until a
frame-compatible realization is provided.

As a route-specific stress test, `ComplexShearGateCostAuditH19H20.lean`
recomputes the h=19 and h=20 ledger when each of its six directional units is
instantiated by this two-scalar-gate bridge.  It replaces the shear term
`6 * shearCharge` by `12 * shearCharge` and verifies exactly:

```text
h = 19:  margin = -178,402,590,
         normalized = -13005 / 1099511627776
h = 20:  margin =  -51,984,000,
         normalized = -3249 / 2199023255552
```

These negative values do not prove a universal lower bound.  They show only
that the current positive h=19/h=20 certificate cannot be claimed for this
explicit scalar-gate instantiation without additional compression, primitive
transvection gates, or a different schedule.

Build with:

```bash
cd lean
lake build \
  OAI.Computability.FourierCircuit.ComplexShearGateBridge \
  OAI.Computability.FourierCircuit.ComplexShearGateCostAuditH19H20
```
