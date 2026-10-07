import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# Three-point arithmetic comparison for the fused-centre candidate

This file evaluates the same conditional one-boundary fusion ledger at
`h = 16, 17, 18`.  It is an exact arithmetic comparison only: no theorem
here supplies a legal fused gate, a frame-labelled terminal interface, or
an all-length Fourier recursion.

The comparison is useful because the padding discontinuities can change the
normalised margin.  With the published role-count formula and the next
power-of-two padding, `h = 18` is the largest of these three candidates.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreBoundaryArithmeticH16H17H18

def value (h : ℕ) : ℕ := Nat.choose h 3
def neighborDegree (h : ℕ) : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def baseCount (h : ℕ) : ℕ := value h ^ 3
def incidenceCount (h : ℕ) : ℕ := 3 * value h ^ 2
def roleCount (h : ℕ) : ℕ :=
  2 * baseCount h + incidenceCount h * (value h * neighborDegree h + h + 1)
def fusedSaving (h : ℕ) : ℕ :=
  2 * baseCount h - 4 * value h ^ 2 * h ^ 2
def shearCharge (h : ℕ) : ℕ := incidenceCount h * h
def fusedMargin (h : ℕ) : ℤ :=
  (fusedSaving h : ℤ) - (shearCharge h : ℤ)
def normalized (h padding : ℕ) : ℚ :=
  (fusedMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

def padding16 : ℕ := 2 ^ 38
def padding17 : ℕ := 2 ^ 39
def padding18 : ℕ := 2 ^ 40

theorem value16_eq : value 16 = 560 := by
  norm_num [value, Nat.choose]

theorem value17_eq : value 17 = 680 := by
  norm_num [value, Nat.choose]

theorem value18_eq : value 18 = 816 := by
  norm_num [value, Nat.choose]

theorem neighborDegree16_eq : neighborDegree 16 = 325 := by
  norm_num [neighborDegree, Nat.choose]

theorem neighborDegree17_eq : neighborDegree 17 = 406 := by
  norm_num [neighborDegree, Nat.choose]

theorem neighborDegree18_eq : neighborDegree 18 = 500 := by
  norm_num [neighborDegree, Nat.choose]

theorem roleCount16_eq : roleCount 16 = 171592825600 := by
  norm_num [roleCount, baseCount, incidenceCount, value, neighborDegree,
    Nat.choose]

theorem roleCount17_eq : roleCount 17 = 383632009600 := by
  norm_num [roleCount, baseCount, incidenceCount, value, neighborDegree,
    Nat.choose]

theorem roleCount18_eq : roleCount 18 = 816132374784 := by
  norm_num [roleCount, baseCount, incidenceCount, value, neighborDegree,
    Nat.choose]

theorem padding16_bounds : 2 ^ 37 < roleCount 16 ∧ roleCount 16 ≤ padding16 := by
  norm_num [roleCount, padding16, baseCount, incidenceCount, value,
    neighborDegree, Nat.choose]

theorem padding17_bounds : 2 ^ 38 < roleCount 17 ∧ roleCount 17 ≤ padding17 := by
  norm_num [roleCount, padding17, baseCount, incidenceCount, value,
    neighborDegree, Nat.choose]

theorem padding18_bounds : 2 ^ 39 < roleCount 18 ∧ roleCount 18 ≤ padding18 := by
  norm_num [roleCount, padding18, baseCount, incidenceCount, value,
    neighborDegree, Nat.choose]

theorem fusedSaving16_eq : fusedSaving 16 = 30105600 := by
  norm_num [fusedSaving, baseCount, value, Nat.choose]

theorem fusedSaving17_eq : fusedSaving 17 = 94329600 := by
  norm_num [fusedSaving, baseCount, value, Nat.choose]

theorem fusedSaving18_eq : fusedSaving 18 = 223727616 := by
  norm_num [fusedSaving, baseCount, value, Nat.choose]

theorem shearCharge16_eq : shearCharge 16 = 15052800 := by
  norm_num [shearCharge, incidenceCount, value, Nat.choose]

theorem shearCharge17_eq : shearCharge 17 = 23582400 := by
  norm_num [shearCharge, incidenceCount, value, Nat.choose]

theorem shearCharge18_eq : shearCharge 18 = 35956224 := by
  norm_num [shearCharge, incidenceCount, value, Nat.choose]

theorem fusedMargin16_eq : fusedMargin 16 = 15052800 := by
  norm_num [fusedMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem fusedMargin17_eq : fusedMargin 17 = 70747200 := by
  norm_num [fusedMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem fusedMargin18_eq : fusedMargin 18 = 187771392 := by
  norm_num [fusedMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem normalized16_eq :
    normalized 16 padding16 = 3675 / 274877906944 := by
  norm_num [normalized, padding16, fusedMargin, fusedSaving, shearCharge,
    baseCount, incidenceCount, value, Nat.choose]

theorem normalized17_eq :
    normalized 17 padding17 = 225 / 8589934592 := by
  norm_num [normalized, padding17, fusedMargin, fusedSaving, shearCharge,
    baseCount, incidenceCount, value, Nat.choose]

theorem normalized18_eq :
    normalized 18 padding18 = 13583 / 463856467968 := by
  norm_num [normalized, padding18, fusedMargin, fusedSaving, shearCharge,
    baseCount, incidenceCount, value, Nat.choose]

theorem normalized16_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 16 padding16 := by
  rw [normalized16_eq]
  norm_num

theorem normalized17_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 17 padding17 := by
  rw [normalized17_eq]
  norm_num

theorem normalized18_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 18 padding18 := by
  rw [normalized18_eq]
  norm_num

theorem normalized17_gt_normalized16 :
    normalized 16 padding16 < normalized 17 padding17 := by
  rw [normalized16_eq, normalized17_eq]
  norm_num

theorem normalized18_gt_normalized17 :
    normalized 17 padding17 < normalized 18 padding18 := by
  rw [normalized17_eq, normalized18_eq]
  norm_num

theorem normalized18_gt_normalized16 :
    normalized 16 padding16 < normalized 18 padding18 := by
  rw [normalized16_eq, normalized18_eq]
  norm_num

end FusedCentreBoundaryArithmeticH16H17H18
end ExactFourier
end OAI
