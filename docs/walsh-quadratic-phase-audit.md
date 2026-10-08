# Walsh frame and quadratic phase instantiation audit

This note records what can be instantiated in the phase interface after the
`v0.2.15` release.  The conclusion is deliberately conservative: the current
repository has the address-conjugation theorem, but it does not yet contain a
normalized Walsh frame or the paper's `q_U` profile.

## Existing definitions that are close, but not instances

* `ExactFourier.SignedBits.J` in `SignedPrice.lean` is a recursively defined
  signed **monomial** matrix.  The available facts are `J_monomial`,
  `J_orthogonal`, and `J_sign`.  A normalized Walsh matrix is dense (for every
  pair of addresses its entry is a nonzero signed scalar), so `J_monomial`
  shows that this `J` cannot be identified with that Walsh matrix for a
  nontrivial address space.  `J_orthogonal` is useful for a future frame, but
  it is not a Walsh-normalization theorem.
* `MinUncut/PCP/Walsh.lean` defines real Walsh characters on a Boolean cube.
  Its index type (`I → Bool`) and codomain (`ℝ`) do not match
  `Address ι := ι → ZMod 2` and the complex matrix interface used by
  `AddressPhaseConjugation.lean`.  A new equivalence and a matrix-lifting
  definition would be required before those characters can be used as `J`.
* `SignedBits.weight` is a weight on the recursive `SignedBits.Bits m` type.
  It is not a weight on `Address ι`, and there is no map from a projected
  address to `Bits m` in the current development.

## Exact missing data for `q_U`

To define the paper's phase profile, the formalization still needs all of the
following explicit choices:

1. an address/subspace API, for example a submodule `U` of the binary address
   space and a linear projection `P_U : Address ι →ₗ[F₂] Address ι` (including
   the complement or orthogonality data that makes the projection canonical);
2. a weight function on binary addresses, such as the cardinality of the
   support of `x : Address ι`, together with its relationship to any selected
   Boolean-cube representation; and
3. the complex profile
   `q_U x = Complex.I ^ (weight (P_U x))` (or the precise phase convention
   used by the target construction).

There is also no theorem that the candidate frame commutes with every needed
address permutation.  This is a separate obligation from orthogonality:
`matrix_conj_framedPhase_of_commutes` requires
`matrix e * J = J * matrix e`, and derives the inverse commutation itself.

Finally, the complex identity needed for a charged step is the nested ratio
`Φ_V * Φ_U⁻¹`.  The existing phase file only proves conjugation of a supplied
`J * diag(q) * J`; it does not prove that ratio or its direction count.

## Safe theorem boundary

The strongest theorem that is currently justified is therefore the existing
generic statement (with `J`, `q`, and the commutation hypothesis supplied by a
future instantiation):

```lean
theorem matrix_conj_framedPhase_of_commutes
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (q : Address ι → ℂ)
    (hJ : matrix e * J = J * matrix e) :
    matrix e * framedPhase J q * (matrix e)⁻¹ =
      framedPhase J (q ∘ (fun x => (induced e).symm x))
```

It is sound to instantiate `q` with `q_U` only after supplying the three
definitions above, and sound to call a matrix `J` a Walsh frame only after
proving its normalization and Walsh character identities.  The current
`SignedBits.J` and the Boolean-cube Walsh characters do not discharge those
obligations.  The next substantive Lean step is consequently to define the
address equivalence, projection, weight, and normalized Walsh matrix together,
then prove the required commutation and nested-`Phi` identity.
