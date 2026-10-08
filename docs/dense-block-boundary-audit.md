# Dense two-frame block-boundary audit

The even-width dense cover uses `u=e₀` and `w=1+e₀` in `F₂²⁴`.  Targets
containing coordinate zero are routed to `w`; the other 1771 targets are
routed to `u`.  The exact Python audit in
`scripts/dense_block_boundary_audit.py` gives the following finite facts:

| block | targets | constraint rank | common boundary |
| --- | ---: | ---: | ---: |
| containing 0 | 253 | 23 | `span(w)` |
| avoiding 0 | 1771 | 23 | `span(u)` |

Every individual target boundary has rank 23.  The target-indexed parity
matrices have exact GF(2) ranks

```text
contains-zero: zero=252, two=253, even=23
avoids-zero:   zero=1770, two=1771, even=23
```

These ranks show that the two-label cover is not by itself a low-rank
side-wire factorization: the target-indexed parity maps retain essentially
full block rank.  The conditional switch-only ledger is 1202 direction units,
leaving `2,425,171,790` against the h=24 centre-compression saving, with
normalised finite margin about `4.98607696×10⁻⁹` under the stated accounting.

The audit is limited to binary labels, block spans, and exact finite-field
ranks.  It does not prove a complex gate realization, a global schedule, an
all-length recurrence, or a lower bound for arbitrary complex circuits.
