import OAI.Computability.FourierCircuit.GlobalFrameTowerBridge

/-!
# Dimension obstruction for the recursive tower lift

`finTowerLift` is a useful label-transport map, but its source and target
address types have different cardinalities.  The fixed-width complex circuit
semantics therefore cannot treat it as a physical wire permutation.  This
module records that type-level obstruction explicitly; it does not rule out a
new construction on one fixed ambient address space.
-/

open OAI ExactFourier

namespace OAI.ExactFourier.TowerDimensionObstruction

theorem no_fixed_width_equiv {h k : ℕ} (hh : 2 ≤ h) :
    ¬ Nonempty (Fin (h ^ (k + 1)) ≃ Fin (h ^ (k + 2))) := by
  intro he
  obtain ⟨e⟩ := he
  have hc := Fintype.card_congr e
  simp only [Fintype.card_fin] at hc
  have hp : h ^ (k + 1) < h ^ (k + 2) := by
    have hlt : 1 < h := by omega
    have hpos : 0 < h ^ (k + 1) := Nat.pow_pos (by omega)
    calc
      h ^ (k + 1) < h * h ^ (k + 1) := by
        simpa [Nat.one_mul] using
          (Nat.mul_lt_mul_of_pos_right hlt hpos)
      _ = h ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
  omega

theorem finTowerLift_is_not_a_permutation {h k : ℕ} (hh : 2 ≤ h) :
    ¬ Nonempty (Fin (h ^ (k + 1)) ≃ Fin (h ^ (k + 2))) :=
  no_fixed_width_equiv hh

end OAI.ExactFourier.TowerDimensionObstruction
