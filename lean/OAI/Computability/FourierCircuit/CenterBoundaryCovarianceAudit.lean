import OAI.Computability.FourierCircuit.CenterBoundaryTensorProjection

/-!
# Covariance audit of the proposed centre-boundary shear

Moving the target line into the *old* boundary is not by itself a change of
frame for the readout.  A consistent isometry transports the target boundary
as well as the line, and preserves their non-membership.  If instead the old
boundary is kept fixed, the proposed transvection does not preserve it: the
legal coordinate line `e_w` is sent to the illegal target line `t`.

The theorems apply at every unit prefix, including h=24.  They rule out the
interpretation of the local shear as a free consistent-frame repair.  They
do not rule out a redesigned circuit with separate transports whose complete
matrix identity and costs are proved independently.
-/

namespace OAI.ExactFourier.CenterBoundaryCovarianceAudit

open CenterBoundaryTensorLift CenterBoundaryTensorProjection
open CenterBoundaryShearCandidate CenterBoundaryObstruction
open SideRowGeneralArbitrary BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

theorem mem_targetPerp_iff {h : ℕ} (t z : Active h) :
    z ∈ targetPerp t ↔ dotProduct t z = 0 := by
  change z ∈ (F ∙ t).orthogonalBilin
      (BinaryTransvection.bilinearDot : _) ↔ _
  rw [Submodule.orthogonalBilin_span_singleton]
  rfl

/-- Transporting both the vector and its boundary preserves membership. -/
theorem targetPerp_transport_iff {h : ℕ}
    (U : Active h ≃ₗ[F] Active h)
    (hU : ∀ v w, dotProduct (U v) (U w) = dotProduct v w)
    (t z : Active h) :
    U z ∈ targetPerp (U t) ↔ z ∈ targetPerp t := by
  rw [mem_targetPerp_iff, mem_targetPerp_iff, hU]

theorem L5_transport_iff {ι : Type*} [Fintype ι] {h : ℕ}
    (U : Active h ≃ₗ[F] Active h)
    (hU : ∀ v w, dotProduct (U v) (U w) = dotProduct v w)
    (p : ι → F) (t : Active h) (z : ι × Fin h → F) :
    lift U z ∈ L5 p (U t) ↔ z ∈ L5 p t := by
  change CenterRowGeneral.project p (lift U z) ∈ targetPerp (U t) ↔
    CenterRowGeneral.project p z ∈ targetPerp t
  rw [project_lift, targetPerp_transport_iff U hU]

theorem raw_target_not_L5 {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) :
    insertP p t ∉ L5 p t := by
  rw [Submodule.mem_comap, project_insertP p hp]
  exact target_line_not_targetPerp t ht

/-- A simultaneous frame change cannot remove the original obstruction. -/
theorem simultaneous_transport_not_L5 {ι : Type*} [Fintype ι] {h : ℕ}
    (U : Active h ≃ₗ[F] Active h)
    (hU : ∀ v w, dotProduct (U v) (U w) = dotProduct v w)
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) :
    lift U (insertP p t) ∉ L5 p (U t) := by
  rw [L5_transport_iff U hU]
  exact raw_target_not_L5 p t hp ht

/-- The proposed repair exchanges one legal line with the missing line. -/
theorem coordinate_legal_but_sheared_illegal
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (w : Fin h) (hw : t w = 0) :
    insertP p (coordinate w) ∈ L5 p t ∧
      lift (unitCoordinateEquiv t w ht hw)
        (insertP p (coordinate w)) ∉ L5 p t := by
  constructor
  · rw [Submodule.mem_comap, project_insertP p hp, mem_targetPerp_iff]
    rw [dot_coordinate]
    exact hw
  · rw [lift_insert, unitCoordinateEquiv_coordinate]
    exact raw_target_not_L5 p t hp ht

/-- In particular, this shear is not an automorphism of the old boundary. -/
theorem shear_does_not_preserve_L5
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (w : Fin h) (hw : t w = 0) :
    ¬ ∀ z ∈ L5 p t, lift (unitCoordinateEquiv t w ht hw) z ∈ L5 p t := by
  intro hpres
  have hwitness := coordinate_legal_but_sheared_illegal p t hp ht w hw
  exact hwitness.2 (hpres _ hwitness.1)

/-- Adding a legal background cannot absorb the nonzero target component. -/
theorem legal_background_add_target_not_L5
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (z : ι × Fin h → F) (hz : z ∈ L5 p t) :
    z + insertP p t ∉ L5 p t := by
  intro hsum
  have htarget := (L5 p t).sub_mem hsum hz
  have heq : z + insertP p t - z = insertP p t := by abel
  rw [heq] at htarget
  exact raw_target_not_L5 p t hp ht htarget

/-- Undoing the selective shear restores the obstruction whenever the
background has also been restored to the old legal row. -/
theorem restored_sheared_readout_not_L5
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (w : Fin h) (hw : t w = 0)
    (z : ι × Fin h → F)
    (hz : lift (unitCoordinateEquiv t w ht hw) z ∈ L5 p t) :
    lift (unitCoordinateEquiv t w ht hw)
      (z + lift (unitCoordinateEquiv t w ht hw) (insertP p t)) ∉ L5 p t := by
  rw [map_add, lift_insert, lift_insert, sheared_line_involutive]
  exact legal_background_add_target_not_L5 p t hp ht _ hz

end OAI.ExactFourier.CenterBoundaryCovarianceAudit
