import OAI.Computability.FourierCircuit.CenterBoundaryShearCandidate
import Mathlib.Tactic

/-!
# Tensor lift for active-factor boundary shears

For a finite prefix type `ι`, this file lifts a linear equivalence on the
active factor `Fin h → ZMod 2` fibrewise to the address space
`ι × Fin h → ZMod 2`.  The lift is an actual linear equivalence, and it
commutes with the prefix insertion `p ⊗ t`.  This discharges the tensor-lift
part of the local shear interface; it does not prove a gate cost or a global
stage schedule.
-/

namespace OAI
namespace ExactFourier
namespace CenterBoundaryTensorLift

open CenterRowGeneral

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} {h : ℕ}

/-- Fibrewise lift of an active-factor linear equivalence. -/
noncomputable def lift (U : Active h ≃ₗ[F] Active h) :
    Address ι h ≃ₗ[F] Address ι h where
  toFun z := fun q => U (fun j => z (q.1, j)) q.2
  invFun z := fun q => U.symm (fun j => z (q.1, j)) q.2
  left_inv z := by
    funext q
    exact congrArg (fun f => f q.2) (U.left_inv (fun j => z (q.1, j)))
  right_inv z := by
    funext q
    exact congrArg (fun f => f q.2) (U.right_inv (fun j => z (q.1, j)))
  map_add' z z' := by
    funext q
    change U (fun j => (z + z') (q.1, j)) q.2 =
      (U (fun j => z (q.1, j)) + U (fun j => z' (q.1, j))) q.2
    rw [show (fun j => (z + z') (q.1, j)) =
        (fun j => z (q.1, j)) + (fun j => z' (q.1, j)) by rfl]
    simp
  map_smul' a z := by
    funext q
    change U (fun j => (a • z) (q.1, j)) q.2 =
      (a • U (fun j => z (q.1, j))) q.2
    rw [show (fun j => (a • z) (q.1, j)) =
        a • (fun j => z (q.1, j)) by rfl]
    simp

@[simp] theorem lift_apply (U : Active h ≃ₗ[F] Active h)
    (z : Address ι h) (q : ι × Fin h) :
    lift U z q = U (fun j => z (q.1, j)) q.2 := rfl

/-- The lift commutes with prefix-active tensor insertion. -/
theorem lift_insert (U : Active h ≃ₗ[F] Active h)
    (p : ι → F) (t : Active h) :
    lift U (insert p t) = insert p (U t) := by
  funext q
  change U (fun j => p q.1 * t j) q.2 = p q.1 * U t q.2
  have hfun : (fun j => p q.1 * t j) = (p q.1) • t := by
    funext j
    simp [smul_eq_mul]
  rw [hfun, U.map_smul]
  rfl

/-- A prefix-specific tensor-lift interface. -/
structure PrefixTensorLiftInterface (p : ι → F) where
  transport : (Active h ≃ₗ[F] Active h) → Address ι h → Address ι h
  insert : Active h → Address ι h
  lift_insert : ∀ (U : Active h ≃ₗ[F] Active h) (t : Active h),
    transport U (insert t) = insert (U t)

/-- The fibrewise lift with the concrete prefix insertion. -/
noncomputable def interface (p : ι → F) : PrefixTensorLiftInterface (h := h) p where
  transport := fun U => lift U
  insert := CenterRowGeneral.insert p
  lift_insert := by
    intro U t
    exact lift_insert U p t

end CenterBoundaryTensorLift
end ExactFourier
end OAI
