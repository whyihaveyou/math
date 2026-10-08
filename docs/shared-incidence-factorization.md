# Shared incidence factorization

`SharedIncidenceFactorization.lean` records the common algebraic feature map behind
both the compressed centre bank and the q-free side moment.

For a source vector `x : Triple h → K`, define

```text
A(x)_i = Σ {x_T | i ∈ T}.
```

The two readouts are linear maps of this same vector:

```text
centre_i(A) = A_i - (Σ_j A_j)/9,
side_S(A) = ((Σ_i A_i)/3 - Σ_{i∈S} A_i)/2.
```

The factorization theorems are

- `compressedG_factor_through_incidence`;
- `sideMomentNoGlobal_factor_through_incidence`.

`incidenceHom` is the additive/scalar-linear version of `A`.  The range
certificate `incidence_range_finrank_le` proves that the common feature range
has `finrank ≤ h`; the concrete `h = 24` theorem gives `≤ 24`.  The output
ranges of each readout and their joint product are bounded by the same rank
using `compressedG_range_finrank_le`,
`sideMomentNoGlobal_range_finrank_le`, and
`jointIncidence_range_finrank_le`.

This is an algebraic information-factorization certificate.  It does not claim
that a frame-preserving complex-gate schedule realizes either readout, nor does
it prove a fixed-width all-length DFT recurrence.
