# Raw centre-boundary fusion no-go

`FusedCentreInvocation.lean` proves the scalar six-row identity: the centre
update and immediate readout can be algebraically fused while arbitrary
centre and side banks are restored.  That identity does not by itself prove
an `E⊗D → B⊗D` frame edge.

`CenterBoundaryFusionNoGo.lean` closes the smallest missing local question.
For a unit prefix `p`, a unit target label `t`, and a source label `x` with
`x·t=0`, the old row-5 boundary is

```text
parent p ⊔ L5 p t = (B ⊗ D) ⊥ (P ⊗ t^⊥).
```

The raw target line `insert p t = p⊗t` is outside that boundary.  The theorem
`raw_fused_readout_not_legal` strengthens this: if `z` is any source-row
vector already in `L2 p x`, then `z + insert p t` is still outside the old
boundary.  The proof subtracts `z`; since `L2 p x ≤ L5 p t`, legality of the
sum would imply legality of the raw line, contradicting the target-line
obstruction.

Therefore the proposed centre fusion needs a real additional interface.  A
valid proof must provide a sheared line, change the target boundary, or cancel
the direct target term before entering row 5.  The theorem is local and does
not claim a lower bound for arbitrary complex circuits.

Compile:

```bash
cd lean
lake env lean OAI/Computability/FourierCircuit/CenterBoundaryFusionNoGo.lean
```
