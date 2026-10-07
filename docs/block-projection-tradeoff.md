# Block-local oblique projection tradeoff (conditional)

A possible way around the coordinate residual is to use an oblique projection
inside blocks of triples that are pairwise even-intersection.  Such a block is
frame-compatible for off-diagonal side roles.  The script
[`scripts/block_projection_tradeoff.py`](../scripts/block_projection_tradeoff.py)
uses a deterministic greedy partition at (h=24); its block-size histogram is

\[
12\times22,\quad 24\times20,\quad 48\times16,\quad 64\times8.
\]

This is a construction for a conditional search, not a claim that every legal
projection is block diagonal.  With centre rank budget (h=24), the best
rank-one oblique model spends its 24 centre dimensions on the largest blocks.
A (k)-block rank-one centre projection can leave only one nonzero residual
diagonal, but its complementary residual has (k^2-k+1) support entries.  The
resulting audit is:

| model | diagonal residual roles | side support roles |
|---|---:|---:|
| coordinate projection | 2,000 | 2,000 |
| block-oblique lower model | 1,544 | 11,648 |

The current h=24 centre saving can absorb at most 98 diagonal channels when a
modified frame charges two directions per diagonal channel.  The (2^{36}
width bucket allows at most 4,218 side roles per invocation.  Thus this
block-local oblique model misses both thresholds: it has too many diagonal
channels and too much support.  More general projections with cancellations
between blocks remain outside this audit and would need an explicit support,
rank, and frame certificate before being claimed.

Run:

```bash
python3 scripts/block_projection_tradeoff.py
```
