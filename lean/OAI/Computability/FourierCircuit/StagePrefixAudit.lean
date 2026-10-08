import OAI.Computability.FourierCircuit.CenterRowGeneral
import OAI.Computability.FourierCircuit.SideRowGeneralArbitrary

/-!
# Prefix-size instantiations for the local centre/side certificates

The paper's three centre/side transitions use different prefix sizes.  This
file instantiates the arbitrary-prefix certificates at `Fin 1`, `Fin h`, and
`Fin (h*h)`.  It checks the directional dimensions only; it does not identify
these abstract coordinate prefixes with the paper's complete eight-row
address schedule.
-/

namespace OAI
namespace ExactFourier
namespace StagePrefixAudit

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

def prefixUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι) : ι → F := BinaryTransvection.coordinate w

def xLabel {h : ℕ} (hh : 1 ≤ h) : Active h :=
  BinaryTransvection.coordinate ⟨0, by omega⟩
def yLabel {h : ℕ} (hh : 2 ≤ h) : Active h :=
  BinaryTransvection.coordinate ⟨1, by omega⟩

def zeroIndex {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def zeroProductIndex {h : ℕ} (hh : 2 ≤ h) : Fin (h * h) :=
  ⟨0, Nat.mul_pos (by omega) (by omega)⟩

def prefixH {h : ℕ} (hh : 2 ≤ h) : Fin h → F :=
  prefixUnit (zeroIndex (by omega))

def prefixHH {h : ℕ} (hh : 2 ≤ h) : Fin (h * h) → F :=
  prefixUnit (zeroProductIndex hh)

def stageX {h : ℕ} (hh : 2 ≤ h) : Active h := xLabel (by omega)
def stageY {h : ℕ} (hh : 2 ≤ h) : Active h := yLabel hh

theorem prefixUnit_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι) :
    dotProduct (prefixUnit w) (prefixUnit w) = (1 : F) := by
  simp [prefixUnit, BinaryTransvection.coordinate,
    Pi.single_apply]

theorem xLabel_unit {h : ℕ} (hh : 1 ≤ h) :
    dotProduct (xLabel (h := h) hh) (xLabel (h := h) hh) = (1 : F) := by
  simp [xLabel, BinaryTransvection.coordinate]

theorem yLabel_unit {h : ℕ} (hh : 2 ≤ h) :
    dotProduct (yLabel (h := h) hh) (yLabel (h := h) hh) = (1 : F) := by
  simp [yLabel, BinaryTransvection.coordinate]

theorem labels_orthogonal {h : ℕ} (hh : 2 ≤ h) :
    dotProduct (xLabel (h := h) (by omega)) (yLabel (h := h) hh) = (0 : F) := by
  simp [xLabel, yLabel, BinaryTransvection.coordinate]

theorem prefix_finranks {h : ℕ} (hh : 2 ≤ h) : (
    (Module.finrank F
        (CenterRowGeneral.residual
          (h := h) (prefixUnit (ι := Fin 1) 0))) = h ∧
      (Module.finrank F
        (CenterRowGeneral.residual
          (h := h) (prefixH hh))) = h ∧
      (Module.finrank F
        (CenterRowGeneral.residual
          (h := h) (prefixHH hh))) = h ∧
      (Module.finrank F
        (SideRowGeneralArbitrary.residual
          (ι := Fin 1) (prefixUnit (ι := Fin 1) 0)
          (stageX hh) (stageY hh))) = h - 2 ∧
      (Module.finrank F
        (SideRowGeneralArbitrary.residual
          (ι := Fin h) (prefixH hh)
          (stageX hh) (stageY hh))) = h - 2 ∧
      (Module.finrank F
        (SideRowGeneralArbitrary.residual
          (ι := Fin (h * h)) (prefixHH hh)
          (stageX hh) (stageY hh))) = (h - 2)) := by
  have hp1 := prefixUnit_unit (ι := Fin 1) 0
  have hph := prefixUnit_unit (ι := Fin h) (zeroIndex (by omega))
  have hphh := prefixUnit_unit (ι := Fin (h * h)) (zeroProductIndex hh)
  have hx := xLabel_unit (h := h) (by omega)
  have hy := yLabel_unit (h := h) hh
  have hxy := labels_orthogonal (h := h) hh
  refine ⟨CenterRowGeneral.residual_finrank _ hp1,
    CenterRowGeneral.residual_finrank _ hph,
    CenterRowGeneral.residual_finrank _ hphh,
    SideRowGeneralArbitrary.residual_finrank _ _ _ hp1 hx hy hxy hh,
    SideRowGeneralArbitrary.residual_finrank _ _ _ hph hx hy hxy hh,
    SideRowGeneralArbitrary.residual_finrank _ _ _ hphh hx hy hxy hh⟩

end StagePrefixAudit
end ExactFourier
end OAI
