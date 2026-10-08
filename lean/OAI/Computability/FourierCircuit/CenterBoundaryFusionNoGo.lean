import OAI.Computability.FourierCircuit.CenterBoundaryObstruction
import Mathlib.Tactic

/-!
# A minimal no-go for raw centre-boundary fusion

The scalar `FusedCentreInvocation` identity removes two scalar rows, but an
`E ⊗ D -> B ⊗ D` fusion also has to place the direct target line in the
row-5 boundary.  This file isolates the exact obstruction for the old
boundary.  The raw line `p ⊗ t` is outside

`parent p ⊔ L5 p t = (B ⊗ D) ⊥ (P ⊗ t^⊥)`.

Adding a source-row vector already in `L2 p x` cannot repair the mismatch:
subtracting that vector from a putative legal readout would put the raw line
itself in the old boundary.  Thus a centre-fusion proof must supply at least
one of the following missing ingredients:

* a sheared target line (as in `CenterBoundaryShearCandidate`),
* a changed target boundary which contains the raw line, or
* a different scalar factorisation whose direct term is cancelled before
  this boundary is entered.

This is a local frame no-go only.  It does not lower-bound arbitrary complex
circuits and does not rule out a future redesigned edge.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryFusionNoGo

open CenterBoundaryObstruction
open CenterRowGeneral
open SideRowGeneralArbitrary

abbrev F := ZMod 2

/- A source-row contribution cannot hide the missing raw target line. -/
theorem raw_fused_readout_not_legal
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Fin h → F)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0)
    (z : SideRowGeneralArbitrary.E ι h)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p x) :
    z + CenterRowGeneral.insert p t ∉
      CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t := by
  intro hlegal
  have hzL5 : z ∈ SideRowGeneralArbitrary.L5 p t :=
    SideRowGeneralArbitrary.L2_le_L5 p x t hxt hz
  have hzBoundary : z ∈
      CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t := by
    exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, z, hzL5, by simp⟩
  have hraw : (z + CenterRowGeneral.insert p t) - z ∈
      CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t :=
    Submodule.sub_mem _ hlegal hzBoundary
  have hline : CenterRowGeneral.insert p t ∈
      CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t := by
    convert hraw using 1 <;> abel
  exact insert_target_not_parent_sup_targetPerp p t hp ht hline

/- The same obstruction as an explicit edge interface.  This is useful for
   a future gate proof: the scalar part may be supplied independently, but a
   raw line edge with the old boundary is inconsistent. -/
structure RawCentreFusionEdgeWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Fin h → F) where
  prefix_unit : dotProduct p p = (1 : F)
  target_unit : dotProduct t t = (1 : F)
  source_target_orthogonal : dotProduct x t = 0
  source_row : SideRowGeneralArbitrary.E ι h
  source_row_mem : source_row ∈ SideRowGeneralArbitrary.L2 p x
  raw_readout_mem : source_row + CenterRowGeneral.insert p t ∈
    CenterRowGeneral.parent p ⊔ SideRowGeneralArbitrary.L5 p t

theorem no_raw_centre_fusion_edge
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Fin h → F)
    (w : RawCentreFusionEdgeWitness p x t) : False := by
  exact raw_fused_readout_not_legal p x t w.prefix_unit w.target_unit
    w.source_target_orthogonal w.source_row w.source_row_mem
    w.raw_readout_mem

end CenterBoundaryFusionNoGo
end ExactFourier
end OAI
