# Parameter scan after global-moment elimination

The exact identity \(\sum_i a_i=3q\) removes one side role at every parameter
\(h\).  The scalar width ledger is therefore

\[
W_h=2\binom h3^3+6h\binom h3^2,
\qquad
\Delta_h=2\binom h3^3-6h^2\binom h3^2.
\]

Scanning the exact integer ledger for \(3\le h\le64\) gives the largest
normalized width candidate at \(h=30\):

\[
v=\binom{30}{3}=4060,
\quad W_{30}=136{,}813{,}880{,}000<2^{37},
\quad \Delta_{30}=44{,}835{,}392{,}000,
\]

\[
\frac{\Delta_{30}}{30^3\,2^{37}}
 =\frac{700553}{57982058496}
 \approx1.2082237\times10^{-5}.
\]

For comparison, the h=24 point is
\(2368333/231928233984\approx1.0211491\times10^{-5}\).  The h=30 number
is a scalar padding improvement only.  The incidence rank remains \(h\), and
the direct \(x_S\) term still requires a frame-compatible direct-input row;
the existing h=24 direct-diagonal ledger is already negative.  No h in this
scan is an all-length DFT or a physical complex-gate result.

Run:

```bash
python3 scripts/side_moment_redundant_scan.py
```
