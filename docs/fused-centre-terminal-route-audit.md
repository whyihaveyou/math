# Fused-centre terminal-route audit at h = 16, 17, 18

`FusedCentreTerminalRouteAudit.lean` connects the three-point fused-centre
ledger to the existing common-frame terminal interface.  It uses one explicit
route-specific premise: the terminal bank has one role for each incidence,
so the correction multiplier is `incidenceCount h`.

For an endpoint common frame (`ell = h` or `ell = h - 1`), the generic
terminal cost is exactly `2`.  Since the exploratory ledger charged one line
per role, this adds exactly one unit per incidence.  The resulting margins are

```text
h = 16: 14,112,000
h = 17: 69,360,000
h = 18: 185,773,824
```

After the same `h^3` and power-of-two padding normalization, each remains
strictly above `10^-9` (the exact inequalities are checked by Lean).

This does not lower the common-frame per-role cost below two.  The endpoint
frames are already the minimum: `terminalCost h ell = 2` exactly when
`ell = h` or `ell = h - 1`; every other integral frame has cost at least six,
which is five extra units over the one-line baseline per role.  The file also
records the corresponding upper bounds for the nonendpoint route under the
same incidence-role model.

The result is therefore a conditional arithmetic route audit.  It does not
construct a legal complex terminal gate, establish scalar/gate commutation,
prove a global schedule, or imply an all-length exact DFT theorem.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.FusedCentreTerminalRouteAudit
```
