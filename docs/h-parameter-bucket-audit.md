# Exact h-parameter bucket audit

The independent script [`h_parameter_bucket_audit.py`](../scripts/h_parameter_bucket_audit.py)
recomputes the conditional q-free side-reuse ledger with exact integers and
rationals. It is a padding/arithmetic audit; it does not construct the direct
`x_S` channel or an all-length schedule.

For `h=24`, the reused width is `17,172,846,592`, so it remains in the
`2^34` bucket. The conditional normalized saving is

```text
2368333 / 231928233984 ≈ 1.0211491 · 10^-5.
```

For `h=30`, the width crosses to `2^37` and the conditional normalized saving
becomes

```text
700553 / 57982058496 ≈ 1.2082237 · 10^-5.
```

An exact scan over `3 ≤ h ≤ 1000` finds `h=30` as the best value for this
conditional ledger. The direct-channel margins remain negative:

```text
h=24: -47,323,645,952
h=30: -356,705,104,000
```

The six-phase fused-boundary arithmetic is also positive in this accounting
model (`h=24 ≈ 1.1050·10^-8`, `h=30 ≈ 2.1581·10^-9`), but both values depend on
the supplied boundary/shear charge assumptions. None of these numbers is an
unconditional DFT exponent theorem.
