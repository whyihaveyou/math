# Pair/complement frame-permutation bridge

`PairComplementFramePermutationBridge.lean` lifts the active-coordinate
permutation from `PairComplementFramePermutation.lean` through a fixed prefix
insertion.  For a pair `F`, define the inserted B-bank support as the range of
the prefix insertion restricted to `disjointTripleSpan F`.  The theorem
`lifted_bank_map_eq` proves the exact transport law

```text
map (lift (activeReindex e)) (insertedDisjointBank p F)
  = insertedDisjointBank p (F.image e).
```

The h=24 specialization `H24.lifted_b_bank_map_eq` and
`H24.b_bank_rank_transport` connect this transport to the pair/complement
candidate's 22-dimensional B-bank.  The rank is permutation invariant, and the
inserted submodule is transported exactly in both directions.

This is a label-space and tensor-lift interface.  It does not prove that the
lift is one legal complex gate, that it commutes with the scalar
pair/complement invocation, or that a family of permutations has a common
global schedule.  Those facts remain explicit physical-circuit premises.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.PairComplementFramePermutation \
  OAI.Computability.FourierCircuit.PairComplementFramePermutationBridge
```

