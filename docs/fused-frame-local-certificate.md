# Fused frame-local certificate

`FusedFrameLocalCertificate.lean` packages one fixed-prefix local witness for
the centre-fusion candidate.  A `Data` value contains:

* a `CenterFramedInvocation.FramedState`, so the source and target labels are
  the labels carried by the frame rather than unrelated free variables;
* a unit prefix, a target coordinate `w` with `target w = 0`, and a source-row
  address `z` in the old `L2` boundary;
* the finite-prefix data needed by the tensor-lift projection theorem.

The theorem `valid` proves the two local facts together:

1. `fusedForward` applies the scalar fused six-row map and restores the
   arbitrary centre/side banks while sending `y` to `y + x`;
2. the source-row contribution plus the fibrewise lifted transvection of the
   inserted target line belongs to the old `L5` boundary.

The companion theorem `valid_with_frame` adds the exact equality that the
fused map leaves the frame labels unchanged.

The result is intentionally not a physical-circuit theorem.  It does not
claim that the binary transvection is one legal complex gate, that the gate
commutes with the scalar six-row map, or that local certificates for every
prefix fit one global DAG.  Those gate, commutation, and global-schedule facts
remain premises for a later all-length DFT construction.

Compile with:

```bash
cd lean
lake env lean OAI/Computability/FourierCircuit/FusedFrameLocalCertificate.lean
```
