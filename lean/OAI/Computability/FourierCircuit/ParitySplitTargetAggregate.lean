import OAI.Computability.FourierCircuit.CenterMap
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Scalar certificate for parity-split target aggregates

For a target triple `S`, split the off-diagonal side correction into the two
nonzero intersection classes:

* `zeroAggregate S x` sums source values with `|S ∩ T| = 0`;
* `twoAggregate S x` sums source values with `|S ∩ T| = 2`.

The readout `zero/2 - two/2` is exactly `sideAction`.  This is a scalar
certificate only: the accompanying frame-cost audit is conditional on the
chosen target-aggregate boundary.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace ParitySplitTargetAggregate

open CenterCompression

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

noncomputable def zeroAggregate (S : Triple h) (x : Triple h → K) : K :=
  ∑ T ∈ (tripleSet h).attach,
    if (S.1 ∩ T.1).card = 0 then x T else 0

noncomputable def twoAggregate (S : Triple h) (x : Triple h → K) : K :=
  ∑ T ∈ (tripleSet h).attach,
    if (S.1 ∩ T.1).card = 2 then x T else 0

noncomputable def splitAction (S : Triple h) (x : Triple h → K) : K :=
  ∑ T ∈ (tripleSet h).attach,
    (if (S.1 ∩ T.1).card = 0 then (1 : K) / 2 else
      if (S.1 ∩ T.1).card = 2 then -(1 : K) / 2 else 0) * x T

/-- The coefficient of the split aggregates agrees with the side coefficient. -/
theorem split_coeff (S T : Triple h) :
    (if (S.1 ∩ T.1).card = 0 then (1 : K) / 2 else
      if (S.1 ∩ T.1).card = 2 then -(1 : K) / 2 else 0) =
      sideCoeff (K := K) S T := by
  classical
  by_cases hST : S = T
  · subst T
    simp [sideCoeff, triple_card]
  · have hlt := inter_card_lt_three S T hST
    by_cases hzero : (S.1 ∩ T.1).card = 0
    · simp [sideCoeff, hST, hzero]
    · by_cases htwo : (S.1 ∩ T.1).card = 2
      · simp [sideCoeff, hST, htwo]
        ring
      · have hone : (S.1 ∩ T.1).card = 1 := by omega
        simp [sideCoeff, hST, hzero, htwo, hone]

/-- The two aggregate banks have exactly the published side readout. -/
theorem splitAction_eq_sideAction (S : Triple h) (x : Triple h → K) :
    splitAction S x = sideAction S x := by
  classical
  unfold splitAction sideAction
  apply Finset.sum_congr rfl
  intro T hT
  exact congrArg (fun z => z * x T) (split_coeff S T)

/-- The parity-split scalar map closes the compressed centre identity. -/
theorem compressed_plus_splitAction (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + splitAction S x = x S := by
  rw [splitAction_eq_sideAction]
  exact compressed_plus_side S x

/-- Expanded invocation form with the two aggregate values exposed. -/
theorem split_invocation_identity
    (S : Triple h) (x y : Triple h → K)
    (a0 a2 : K) (c : Fin h → K) :
    (y S - a0 / 2 + a2 / 2 - compressedR S c) +
        compressedR S (fun i => c i + compressedG (K := K) x i) +
        (a0 / 2 - a2 / 2 + sideAction S x) =
      y S + x S := by
  have hcenter :
      compressedR S (fun i => c i + compressedG (K := K) x i) =
        compressedR S c + compressedR S (compressedG (K := K) x) := by
    unfold compressedR
    rw [Finset.sum_add_distrib]
    ring
  rw [hcenter]
  have hmain := compressed_plus_side (S := S) (x := x)
  calc
    (y S - a0 / 2 + a2 / 2 - compressedR S c) +
          (compressedR S c + compressedR S (compressedG (K := K) x)) +
          (a0 / 2 - a2 / 2 + sideAction S x) =
        y S + (compressedR S (compressedG (K := K) x) + sideAction S x) := by ring
    _ = y S + x S := by rw [hmain]

end ParitySplitTargetAggregate
end ExactFourier
end OAI
