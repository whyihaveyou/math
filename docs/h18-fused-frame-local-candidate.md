# h = 18 fused-centre frame-local candidate

`H18FusedFrameLocalCandidate.lean` instantiates the generic fused-frame
certificate at `h = 18`.

The file checks, in one fixed `Fin 1` prefix frame:

* the embedded source and target labels are unit and orthogonal;
* the centre and side residual dimensions are exactly `18` and `16`;
* the fused scalar invocation restores arbitrary scalar banks and preserves
  the frame label;
* the tensor-lifted sheared target readout remains in the old `L5` boundary
  under its explicit local hypotheses.

The accompanying arithmetic theorem gives

```text
1 / 10^9 < 13583 / 463856467968
```

for the h=18 one-boundary ledger and its stated power-of-two padding.  This
inequality is conditional arithmetic.  The file does not prove a legal complex
gate, scalar/gate commutation, a common global DAG, the terminal bank route,
or an all-length exact DFT theorem.  In particular, the separate terminal
audit still rules out the exploratory one-line common-frame charge.

Compile with:

```bash
cd lean
lake build OAI.Computability.FourierCircuit.H18FusedFrameLocalCandidate
```
