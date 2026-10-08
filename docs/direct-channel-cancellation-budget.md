# Direct-channel cancellation budget

The q-free side moment and the compressed centre readout cancel exactly:

\[
  R G(x)+V(x)=0.
\]

Here `G` is the shifted centre map and `V` is the side moment reconstructed
from the incidence moments. Therefore an identity of the form

\[
  R G(x)+V(x)+D(x)=x
\]

forces `D(x)=x` for every source bank `x`. The Lean theorem
`direct_forced_identity` proves this pointwise and `direct_forced_surjective`
records the resulting full-rank direct map. A rank-complement estimate does
not make this particular direct channel smaller.
The companion theorem `direct_factorization_finrank_lower_bound` makes the
same obstruction explicit for an additive factorization through an auxiliary
space: if `U ∘ V` realizes this identity, the source-bank finite dimension is
at most the auxiliary dimension, so this model has no lower-rank shortcut.

Under the explicit accounting premise that one full direct coordinate costs at
least one frame unit per invocation, the `3v^2` target invocations cost

\[
  3v^2\cdot v=3v^3.
\]

The uncharged centre saving is at most `2v^3`, so the margin is negative for
every `v>0`, independently of `h`. This is a conditional budget obstruction
for the fixed q-free construction, not a lower bound for arbitrary complex
circuits or for a redesigned direct gate with another charge model.

At `h=24`, sharing the same incidence bank between centre and side lowers the
scalar role count to

\[
  16{,}877{,}893{,}120 < 2^{34},
\]

saving `294,953,472` roles relative to the two-bank q-free ledger. The power
of two padding remains `2^34`, so this sharing is a memory/role improvement;
it does not by itself improve the normalized exponent. A physical frame
transport for this bank and a direct complex gate for `D=id` remain open.

The exact statements are in
[`DirectChannelCancellationBudget.lean`](../lean/OAI/Computability/FourierCircuit/DirectChannelCancellationBudget.lean)
and the shared incidence factorization is in
[`SharedIncidenceFactorization.lean`](../lean/OAI/Computability/FourierCircuit/SharedIncidenceFactorization.lean).
