# Exact side-map rank obstruction for linear multi-stage copies

For `h = 24`, let `V` be the 2024 three-element subsets of `[24]`. The
centre-compressed scalar identity has side correction matrix

\[
 A_{S,T}=\begin{cases}
 +1/2,&|S\cap T|=0,\\
 -1/2,&|S\cap T|=2,\\
 0,&\text{otherwise}.
 \end{cases}
\]

Set `M = 2 A = B_0 - B_2`, where `B_k` records intersection size `k`.
The exact script [`scripts/side_multistage_rank_audit.py`](../scripts/side_multistage_rank_audit.py)
works in the four-dimensional Johnson intersection algebra. It computes the
intersection-class products and verifies

\[
 (M-1267 I)(M+229 I)(M-2 I)=0.
\]

The polynomial is
`z^3 - 1040 z^2 - 288067 z + 580286`; its constant term is nonzero. Thus
`M` and `A` are invertible, so

\[
\operatorname{rank}_{\mathbb Q}(A)=|V|=\binom{24}{3}=2024.
\]

Any linear additive redesign using several side banks factors the correction
as `A = Σ_i J_i V_i`, where bank `i` has dimension `r_i`. Rank subadditivity
then gives `2024 ≤ Σ_i r_i`. Therefore multiple linear copies cannot reduce
the **total** number of side-bank coordinates. This is a conditional
obstruction: it does not cover nonlinear circuits, a different charge model,
or designs where the side coordinates are not auxiliary linear factors.

The certificate is exact; no floating-point rank calculation is used. The
four-class coefficients and the polynomial identity are emitted by the script
and are checked by assertions.

The abstract factorization inequality is also formalized in
[`lean/OAI/Computability/FourierCircuit/LinearMultistageRank.lean`](../lean/OAI/Computability/FourierCircuit/LinearMultistageRank.lean): for `q` copies of one finite-dimensional bank `R`,
`finrank X ≤ q * finrank R` whenever the composed correction is surjective.
Heterogeneous banks can be bundled into their finite product, so the script's
`Σ_i r_i` formulation is the corresponding general statement.
