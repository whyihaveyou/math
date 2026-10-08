import OAI.Computability.FourierCircuit.CenterBoundaryShearCandidate
import Mathlib.Tactic

/-!
# Local frame inclusion for the fused centre readout

The scalar fused invocation reads `R (c + G x)`.  This file records the local
label fact needed when its two summands are separated by the old boundary:
the centre/readout contribution lies in the old source row `L2`, while the
new direct contribution is transported by the reversible shear into `L5`.
The sum is therefore legal in the old target boundary.  This is still a local
submodule statement; it does not define the tensor lift or the global gate.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryFusedReadout

open CenterBoundaryShearCandidate
open CenterFrameDirectionAudit
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-- A source-row contribution plus a sheared direct target line is legal at
    the old target-side boundary. -/
theorem fused_readout_mem_L5
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (x t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0)
    (w : Fin h) (hw : t w = 0)
    (z : SideRowGeneralArbitrary.E ι h)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p x) :
    z + SideRowGeneralArbitrary.insertP p
        (unitCoordinateEquiv t w ht hw t) ∈
      SideRowGeneralArbitrary.L5 p t := by
  apply add_mem
  · exact SideRowGeneralArbitrary.L2_le_L5 p x t hxt hz
  · exact sheared_insert_mem_L5 p t hp ht w hw

/-- Concrete h=24 instance for the audited first-prefix source/target pair. -/
theorem h24_fused_readout_mem_L5
    (z : SideRowGeneralArbitrary.E (Fin 1) 24)
    (hz : z ∈ SideRowGeneralArbitrary.L2
      (StagePrefixAudit.prefixUnit (ι := Fin 1) 0) sourceVec) :
    z + SideRowGeneralArbitrary.insertP
        (StagePrefixAudit.prefixUnit (ι := Fin 1) 0)
        (unitCoordinateEquiv targetVec w targetVec_unit targetVec_zero_at_w targetVec)
      ∈ SideRowGeneralArbitrary.L5
        (StagePrefixAudit.prefixUnit (ι := Fin 1) 0) targetVec := by
  exact fused_readout_mem_L5
    (StagePrefixAudit.prefixUnit (ι := Fin 1) 0)
    sourceVec targetVec
    (StagePrefixAudit.prefixUnit_unit (ι := Fin 1) 0)
    targetVec_unit source_target_vec_orthogonal
    w targetVec_zero_at_w z hz

end CenterBoundaryFusedReadout
end ExactFourier
end OAI
