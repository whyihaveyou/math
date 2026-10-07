import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# h=19 and h=20 fused-centre arithmetic stress test

This file evaluates the same conditional fused-centre ledger used by the
h=16,17,18 comparison, but records the next padding plateau explicitly.
The six-phase number subtracts six copies of the directional shear charge
`I*h`; it is therefore a schedule-level arithmetic candidate, not a
gate-level construction.  No theorem here supplies complex scalar/gate
semantics, a physical frame-preserving schedule, a terminal interface, or an
all-length DFT recursion.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreBoundaryArithmeticH19H20

def value (h : ℕ) : ℕ := Nat.choose h 3
def neighborDegree (h : ℕ) : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def baseCount (h : ℕ) : ℕ := value h ^ 3
def incidenceCount (h : ℕ) : ℕ := 3 * value h ^ 2
def roleCount (h : ℕ) : ℕ :=
  2 * baseCount h + incidenceCount h * (value h * neighborDegree h + h + 1)
def fusedSaving (h : ℕ) : ℕ :=
  2 * baseCount h - 4 * value h ^ 2 * h ^ 2
def shearCharge (h : ℕ) : ℕ := incidenceCount h * h
def sixPhaseMargin (h : ℕ) : ℤ :=
  (fusedSaving h : ℤ) - 6 * (shearCharge h : ℤ)
def normalized (h padding : ℕ) : ℚ :=
  (sixPhaseMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

def padding19 : ℕ := 2 ^ 41
def padding20 : ℕ := 2 ^ 42

theorem value19_eq : value 19 = 969 := by
  norm_num [value, Nat.choose]

theorem value20_eq : value 20 = 1140 := by
  norm_num [value, Nat.choose]

theorem neighborDegree19_eq : neighborDegree 19 = 608 := by
  norm_num [neighborDegree, Nat.choose]

theorem neighborDegree20_eq : neighborDegree 20 = 731 := by
  norm_num [neighborDegree, Nat.choose]

theorem roleCount19_eq : roleCount 19 = 1661448297294 := by
  norm_num [roleCount, baseCount, incidenceCount, value, neighborDegree,
    Nat.choose]

theorem roleCount20_eq : roleCount 20 = 3252070954800 := by
  norm_num [roleCount, baseCount, incidenceCount, value, neighborDegree,
    Nat.choose]

theorem padding19_bounds : 2 ^ 40 < roleCount 19 ∧ roleCount 19 ≤ padding19 := by
  norm_num [roleCount, padding19, baseCount, incidenceCount, value,
    neighborDegree, Nat.choose]

theorem padding20_bounds : 2 ^ 41 < roleCount 20 ∧ roleCount 20 ≤ padding20 := by
  norm_num [roleCount, padding20, baseCount, incidenceCount, value,
    neighborDegree, Nat.choose]

theorem fusedSaving19_eq : fusedSaving 19 = 463846734 := by
  norm_num [fusedSaving, baseCount, value, Nat.choose]

theorem fusedSaving20_eq : fusedSaving 20 = 883728000 := by
  norm_num [fusedSaving, baseCount, value, Nat.choose]

theorem shearCharge19_eq : shearCharge 19 = 53520777 := by
  norm_num [shearCharge, incidenceCount, value, Nat.choose]

theorem shearCharge20_eq : shearCharge 20 = 77976000 := by
  norm_num [shearCharge, incidenceCount, value, Nat.choose]

theorem sixPhaseMargin19_eq : sixPhaseMargin 19 = 142722072 := by
  norm_num [sixPhaseMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem sixPhaseMargin20_eq : sixPhaseMargin 20 = 415872000 := by
  norm_num [sixPhaseMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem normalized19_eq :
    normalized 19 padding19 = 2601 / 274877906944 := by
  norm_num [normalized, padding19, sixPhaseMargin, fusedSaving, shearCharge,
    baseCount, incidenceCount, value, Nat.choose]

theorem normalized20_eq :
    normalized 20 padding20 = 3249 / 274877906944 := by
  norm_num [normalized, padding20, sixPhaseMargin, fusedSaving, shearCharge,
    baseCount, incidenceCount, value, Nat.choose]

theorem normalized19_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 19 padding19 := by
  rw [normalized19_eq]
  norm_num

theorem normalized20_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 20 padding20 := by
  rw [normalized20_eq]
  norm_num

theorem normalized20_gt_normalized19 :
    normalized 19 padding19 < normalized 20 padding20 := by
  rw [normalized19_eq, normalized20_eq]
  norm_num

end FusedCentreBoundaryArithmeticH19H20
end ExactFourier
end OAI
