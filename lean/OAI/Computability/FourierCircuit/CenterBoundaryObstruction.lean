import OAI.Computability.FourierCircuit.CenterMap
import OAI.Computability.FourierCircuit.SideRowGeneralArbitrary
import Mathlib.Tactic

/-!
# Local obstruction to deleting the centre boundary drop

The target row after a centre readout contains the prefix-parent component and
the target-label orthogonal component.  The inserted target line itself is
outside this frame.  The scalar compressed centre map has a nonzero diagonal
coefficient, so this missing line is actually used by the centre readout.
This file proves those two local facts; it does not claim a lower bound for a
different boundary or a different scalar factorization.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryObstruction

open CenterCompression
open CenterRowGeneral
open SideRowGeneralArbitrary

abbrev F := ZMod 2

/- The diagonal entry of `R G` is one for every triple. -/
theorem compressed_center_diagonal {h : ℕ} (S : Triple h) :
    compressedR S
        (compressedG (K := ℚ) (fun U => if U = S then 1 else 0)) = 1 := by
  rw [compressed_RG_basis]
  norm_num [triple_card S]

/- The target line is not contained in its target orthogonal hyperplane. -/
theorem target_line_not_targetPerp {h : ℕ} (t : Fin h → F)
    (ht : dotProduct t t = (1 : F)) :
    t ∉ SideRowGeneralArbitrary.targetPerp t := by
  intro htperp
  change t ∈ (F ∙ t).orthogonalBilin
    (BinaryTransvection.bilinearDot : _) at htperp
  rw [Submodule.orthogonalBilin_span_singleton] at htperp
  change dotProduct t t = 0 at htperp
  rw [ht] at htperp
  exact one_ne_zero htperp

/-
The inserted target line cannot be carried by the parent prefix component
plus the target-side row.  This is the exact `P ⊗ t` versus
`(B ⊗ D) ⊥ (P ⊗ t^⊥)` mismatch used in the centre-boundary audit.
-/
theorem insert_target_not_parent_sup_targetPerp
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (t : Fin h → F)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) :
    insertP p t ∉
      CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t := by
  intro hz
  rcases Submodule.mem_sup.mp hz with ⟨u, hu, v, hv, huv⟩
  have hproj_u : projectP p u = 0 := LinearMap.mem_ker.mp hu
  have hproj_v : projectP p v ∈ targetPerp t := by
    exact (Submodule.mem_comap.mp hv)
  have hproj_eq : t = projectP p v := by
    calc
      t = projectP p (insertP p t) := by rw [project_insertP p hp]
      _ = projectP p (u + v) := by rw [← huv]
      _ = projectP p u + projectP p v := by rw [map_add]
      _ = projectP p v := by rw [hproj_u, zero_add]
  have htv : t ∈ targetPerp t := by
    convert hproj_v using 1
  exact target_line_not_targetPerp t ht htv

end CenterBoundaryObstruction
end ExactFourier
end OAI
