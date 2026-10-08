# Binary frame labels and complex array semantics

The exact model uses two spaces with different scalars.  In the proof source
(`work/external-audit/dft.clean.txt`, §2.2), the label space is
`D = F₂^m` with its ordinary dot product; projections, orthogonal complements,
and nondegeneracy are all over `F₂`.  The complex array has addresses in `D`.
For a label `U`, the proof defines a complex frame operator

\[
  \Phi_U = J_m\,\operatorname{diag}_x(i^{\operatorname{wt}(P_Ux)})\,J_m,
\]

where `J_m` is the normalized Walsh matrix.  Thus a label is a subspace used
to construct a complex matrix; it is not a complex data vector.  There is no
map `F₂ → ℂ` in the construction.

The charged-step lemma is conditional on nested nondegenerate labels
`U ⊆ V` and an orthonormal basis of the residual `U^\perp ∩ V`; it factors
`Φ_V Φ_U⁻¹` into one directional kernel per residual basis vector.  The
network then changes binary address coordinates by an invertible map so a
residual vector becomes a coordinate bit.  This address change is monomial
work, and the directional kernel acts on the selected bit fibers.

`BinaryAddressPermutation.lean` formalizes precisely this free part: a binary
linear equivalence induces a permutation matrix over `ℂ`, with monomiality,
inverse, conjugation, and matrix-unit transport proved.  The support map in
`BinaryComplexFrameMap.lean` is useful only as a warning: it cannot model the
paper's global semantics, because no nonzero additive map `F₂ → ℂ` exists.

For the selective centre candidate, the immediate missing theorem is therefore
not a support-map/shear identity.  It is a legal frame-chain theorem: construct
nested nondegenerate labels (or prove an explicit factorization into nested
steps) from the source endpoint to the target endpoint, certify orthonormal
residuals, and identify the resulting `Φ`-ratio with the scalar network's
required frame transition.  The current selective source/target spaces are
incomparable, so the direct edge cannot receive a Lemma-2.2 residual cost;
its local `W` transport remains a binary subspace fact only.
