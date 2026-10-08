# Conditional h=24 exponent-gap certificate

This note documents the exact claim added in release `v0.2.35-conditional-exponent-gap`.

## Statement

The six-phase h=24 centre ledger in
`OAI.Computability.FourierCircuit.CenterBoundaryShearScheduleAudit` has exact
normalized saving

```text
ε = 2624369 / 237494511599616.
```

`OAI.Computability.FourierCircuit.FusedCentreExponentGapAudit` defines the
corresponding inherited-recurrence exponent gap by

```text
δ = -log(1 - ε) / log(13824)
```

and proves

```text
1 / 10^9 < δ.
```

The proof is fully checked by Lean. It establishes the analytic conversion of
this finite ledger; it does not establish the physical circuit construction
needed to use the ledger in an exact DFT algorithm.

## Proof ingredients

The module proves the exact rational identity for `ε`, positivity and
`ε < 1`, and the bound `11/10^9 < ε`. It proves `log 13824 < 11` from a
finite exponential-series bound and uses the standard inequality
`log(1 - ε) ≤ -ε`. Since `log 13824 > 0`, these inequalities imply the strict
`10^-9` lower bound for `δ`.

## Validation

Run from the repository root:

```bash
lake build OAI.Computability.FourierCircuit.FusedCentreExponentGapAudit
```

The supporting transport certificate is checked with:

```bash
lake build OAI.Computability.FourierCircuit.FusedCentreTransportNaturality
```

## Boundary of the claim

The result is conditional on two supplied premises:

1. the six-phase event-count ledger is the realized cost of the proposed
   centre transport; and
2. the recurrence has multiplier `13824 · (1 - ε)`.

The repository still needs a legal selective complex-gate realization, a
frame-preserving schedule that works across all required prefix types, and the
source/readout and recurrence lemmas needed for an all-length exact DFT
algorithm. No unconditional `O(n (log n)^(1-δ))` theorem is claimed here.
