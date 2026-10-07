import OAI.Computability.FourierCircuit.CenterBoundaryTensorLift
import OAI.Computability.FourierCircuit.CenterBoundaryFusedReadout
import Mathlib.Tactic

/-!
# Projection transport for the tensor-lifted centre shear

The fibrewise active-factor lift is useful for the circuit only if it also
commutes with the prefix contraction used by the row labels.  This file proves
that commutation and then combines it with the local fused-readout boundary
lemma.  The result is still a fixed-prefix frame certificate: it does not
provide the global stage schedule or a complex gate cost.
-/

namespace OAI
namespace ExactFourier
namespace CenterBoundaryTensorProjection

open CenterRowGeneral
open CenterBoundaryTensorLift
open CenterBoundaryShearCandidate
open CenterBoundaryFusedReadout
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] {h : ℕ}

theorem project_lift (U : Active h ≃ₗ[F] Active h)
    (p : ι → F) (z : Address ι h) :
    CenterRowGeneral.project p (lift U z) =
      U (CenterRowGeneral.project p z) := by
  classical
  funext j
  change dotProduct p (fun i => U (fun k => z (i, k)) j) =
    U (fun k => dotProduct p (fun i => z (i, k))) j
  simp only [dotProduct]
  have hsum : (fun k => ∑ i : ι, p i * z (i, k)) =
      ∑ i : ι, p i • (fun k => z (i, k)) := by
    funext k
    simp [smul_eq_mul]
  rw [hsum, map_sum]
  simp [smul_eq_mul]

theorem project_lift_insert (U : Active h ≃ₗ[F] Active h)
    (p : ι → F) (hp : dotProduct p p = (1 : F)) (t : Active h) :
    CenterRowGeneral.project p (lift U (CenterRowGeneral.insert p t)) = U t := by
  rw [lift_insert]
  exact CenterRowGeneral.project_insert p hp (U t)

/- The active-factor shear is now visible as an actual address-space line in
   the old target boundary.  This is the fixed-prefix gate-label interface
   needed before one can discuss a global schedule. -/
theorem lifted_sheared_readout_mem_L5
    (p : ι → F) (x t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0)
    (w : Fin h) (hw : t w = 0)
    (z : E ι h)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p x) :
    z + lift (unitCoordinateEquiv t w ht hw)
        (CenterRowGeneral.insert p t) ∈
      SideRowGeneralArbitrary.L5 p t := by
  rw [lift_insert]
  exact fused_readout_mem_L5 p x t hp ht hxt w hw z hz

end CenterBoundaryTensorProjection
end ExactFourier
end OAI
