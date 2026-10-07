# Centre-boundary shear schedule interface

The local binary transvection certificate repairs a direct target line: for a
unit active label t and a zero coordinate w, `unitCoordinateEquiv t w` sends
t into t^⊥. The schedule audit records the exact conditional price of using
that repair across the centre roles.

At h=24, the fused-centre arithmetic has saving

    7,144,428,544

before the shear charge. Charging one active direction per centre role costs
I₀h=294,953,472. The explicit lift-and-return event model charges six phases,
6I₀h=1,769,720,832, and leaves the normalized margin

    2,624,369 / 237,494,511,599,616 ≈ 1.10502×10⁻⁸ > 10⁻⁹.

`CenterBoundaryShearScheduleAudit.lean` now exposes the remaining obligation
as a machine-checkable interface. A future physical schedule must provide a
finite step type with a surjective assignment to the three-stage,
forward/return event set. If it also proves an upper bound of 6I₀h steps,
Lean forces the step count to equal the six-phase ledger and derives the
strict 10⁻⁹ margin.

The active-factor tensor lift and its projection/readout boundary law are now
proved locally in `CenterBoundaryTensorLift.lean` and
`CenterBoundaryTensorProjection.lean`. The result is still conditional: the
file does not construct the complex gate, prove scalar commutation for the
full eight-row state, or give global restoration across all prefix types. The
upper-bound premise is exactly the part a gate-level implementation must
supply; it is not assumed as an established circuit theorem.

Compile:

```bash
cd lean
lake env lean OAI/Computability/FourierCircuit/CenterBoundaryShearScheduleAudit.lean
```
