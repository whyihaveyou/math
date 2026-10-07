# Pair/complement frame-transport candidate

`PairComplementFrameTransportCandidate.lean` packages the two local transport
layers into one h=24 premise.  For every active-coordinate equivalence `e` and
pair `F`, it proves exact transport of the binary B-bank and, for every unit
first-prefix `p`, exact transport of the inserted tensor B-bank.  It also joins
those facts with the previously checked rank and aggregate-wise integer ledger.

The resulting `H24FrameCompatibleLedgerWithTransport` is a usable interface for
a later physical-circuit proof.  It is still a premise package: no theorem in
this file claims that `liftedReindex` is one legal complex gate, that it
commutes with the scalar pair/complement map, or that a family of permutations
has a common all-prefix DAG and schedule.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.PairComplementFrameTransportCandidate
```

The package also re-exports the exact h=24 scalar identity from
`PairComplementInvocation`: the compressed centre readout plus the two-bank
pair aggregate readout recovers the source map.  Thus the A/B transport facts
now correspond to both banks used by the verified scalar identity; physical
complex-gate realization and all-prefix scheduling remain separate premises.
