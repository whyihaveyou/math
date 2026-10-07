import OAI.Computability.FourierCircuit.CenterMap
import Mathlib.Tactic

/-!
# Scalar certificate for target-indexed side aggregates

This is an independent research file.  It replaces the ordered side array
`A_{S,T}` by one arbitrary aggregate `a_S` per target triple.  The aggregate
is updated by the already proved side correction `sideAction`; hence the
frame question is isolated from the scalar identity.
-/

namespace OAI
namespace ExactFourier
namespace TargetSideAggregate

open OAI.ExactFourier.CenterCompression

theorem aggregate_invocation_identity
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x y a : Triple h → K)
    (c : Fin h → K) :
    (y S - a S - compressedR S c) +
      compressedR S (fun i => c i + compressedG (K := K) x i) +
        (a S + sideAction S x) =
      y S + x S := by
  have hcenter :
      compressedR S (fun i => c i + compressedG (K := K) x i) =
        compressedR S c + compressedR S (compressedG (K := K) x) := by
    unfold compressedR
    rw [Finset.sum_add_distrib]
    ring
  rw [hcenter]
  calc
    (y S - a S - compressedR S c +
          (compressedR S c + compressedR S (compressedG (K := K) x)) +
          (a S + sideAction S x)) =
        y S + (compressedR S (compressedG (K := K) x) + sideAction S x) := by ring
    _ = y S + x S := by rw [OAI.ExactFourier.CenterCompression.compressed_plus_side S x]

end TargetSideAggregate
end ExactFourier
end OAI
