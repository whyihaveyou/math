# Shared parity-bank boundary audit

The local parity certificate is target indexed.  For one target triple `S`,
the source labels with

```text
|S ∩ T| = 0  or  |S ∩ T| = 2
```

are in the target boundary `t_S^⊥` over `F₂`.  This note asks whether the
same source bank could be reused for every target while remaining in one
target-independent frame.

The exact audit is [`scripts/parity_shared_boundary_audit.py`](../scripts/parity_shared_boundary_audit.py).
It uses only bit-vector Gaussian elimination, so its rank claims are finite
and reproducible.  Running

```text
python3 scripts/parity_shared_boundary_audit.py
```

at `h = 24` gives `v = C(24,3) = 2,024` target/source triples and the
following results.

## A literal common-label bank cannot share a target boundary

For every source triple `T`, there is a target `S` disjoint from `T`; hence
the zero-intersection bank, after taking its union over all targets, contains
every triple indicator.  There is also a target with exactly two elements in
common with `T`, so the same is true of the two-intersection bank.  The exact
GF(2) ranks are therefore

```text
global zero-bank label union: 24
global two-bank label union:  24
active label dimension:       24
```

For one fixed target the boundary has dimension `23`.  The global union has
full dimension `24`, and the script finds an odd-overlap witness for every one
of the `2,024` targets (for `S=(0,1,2)`, one witness is `T=(0,3,4)`).  Thus,
under the explicit premise that a common bank literally contains the local
source labels, neither parity bank can lie in any fixed target boundary.  A
target-dependent frame change, a nonlinear source formation, or an
interactive route is outside this statement.

The local ranks for comparison are

```text
fixed-target zero class: 21
fixed-target two class:  23
fixed-target boundary:   23
```

This is why the local `23`-dimensional containment does not transport to one
global `23`-dimensional frame.

## A linear common-bank factorization has a sharp channel floor

Let `A₂` be the `2,024 × 2,024` integer incidence matrix

```text
A₂[S,T] = 1  iff  |S ∩ T| = 2,
           0  otherwise.
```

The bit-vector audit reports exact GF(2) ranks

```text
rank(A₀)       = 2,000    (|S ∩ T| = 0)
rank(A₂)       = 2,024    (|S ∩ T| = 2)
rank(A₀ + A₂)  = 24       (even intersection, modulo 2)
```

The full GF(2) rank of the square integer matrix `A₂` means its determinant is
odd, hence nonzero over `Q` and every characteristic-zero extension such as
`C`.  Consequently, if a target-independent linear bank/readout is required
to factor the two-class aggregate as

```text
A₂ = R · B,
```

with `B` producing `k` common bank channels, then `k ≥ rank(A₂) = 2,024`.
This rules out reducing the parity map to a small (`O(h)`) common linear bank
under that premise.  It does not rule out a different nonlinear or
interactive circuit, and it is not a lower bound for arbitrary complex linear
circuits outside this factorization model.

The result is therefore a route obstruction rather than a universal circuit
lower bound: the local frame-compatible parity labels remain valid, but a
shared frame with zero amortized residual charge needs a construction that
avoids both literal label pooling and the linear factorization above.
