# Frame-labelled pair/complement invocation

`PairComplementFramedInvocation.lean` attaches the audited h=24
`PrefixFrame` to the exact scalar state from `PairComplementInvocation`.  Its
forward, inverse, and three-invocation exchange maps preserve the frame label
and inherit the scalar restoration identities for the two pair banks, the
direct diagonal bank, and the centre map.  The `h24` constructor attaches the
concrete first-prefix frame to any scalar state.

This is a local frame certificate.  It does not identify the scalar maps with
legal complex gates, prove scalar/gate commutation, or provide a global
all-prefix schedule.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.PairComplementFramedInvocation
```
