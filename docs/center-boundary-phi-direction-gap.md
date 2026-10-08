# Selective centre and the `Phi` direction-step gap

`CenterBoundarySelectiveFrameEquiv.lean` proves that the binary transvection
`W` maps the complete selected source label onto the complete selected target
label and is an isometry on that restricted space.  That fact does not yet
give a directional kernel in the paper's `Phi_V Phi_U⁻¹` lemma.

`CenterBoundaryPhiDirectionGap.lean` formalizes the missing input as
`NestedResidualRankWitness`: one endpoint must be nested in the other, with an
orthogonal residual decomposition and a direction count equal to the residual
finrank.  The current selective source and target are incomparable in both
orientations, so no such witness exists for them.  Passing through their
common join costs exactly one residual dimension in each direction, hence two
for a round trip.

This is a precise audit of the frame-label and direction-step interface.  It is
not a complex `Phi` factorization, a gate schedule, or an all-length DFT
theorem.  A future improvement must either prove a permutation-gauged `Phi`
conjugacy with its phase correction, or supply a different nested endpoint
chain.
