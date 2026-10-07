import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# h = 18 p = 1 one-stage candidate

This file is an exact arithmetic and scalar-map certificate for a proposed
one-stage recursive block.  It deliberately does not claim the frame-labelled
network, the address correction, or the all-length Fourier recursion.
-/

namespace OAI
namespace ExactFourier
namespace H18OneStageCandidate

/- The terminal pointwise bank map sends (x, y + x) to (-y, x). -/
def bankGate {α : Type*} [AddCommGroup α] (x y : α) : α × α :=
  (x - y, x)

theorem bankGate_shear {α : Type*} [AddCommGroup α] (x y : α) :
    bankGate x (y + x) = (-y, x) := by
  simp only [bankGate]
  ext <;> dsimp <;> abel

namespace Parameters

def h : ℕ := 18
def v : ℕ := Nat.choose h 3
def neighborDegree : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def n : ℕ := v
def m : ℕ := h
def roleCount : ℕ := 2 * n + v * neighborDegree + h
def batchSize : ℕ := 2 ^ 19
def centerLoss : ℕ := h ^ 2
def deficit : ℕ := n - 2 * centerLoss
def residualBudget : ℕ := roleCount * m - deficit
def lambda : ℚ := (m : ℚ) - (deficit : ℚ) / (batchSize : ℚ)
def epsilon : ℚ := (deficit : ℚ) / ((m : ℚ) * (batchSize : ℚ))

@[simp] theorem h_value : h = 18 := by rfl
@[simp] theorem v_value : v = 816 := by
  norm_num [v, h, Nat.choose]
@[simp] theorem neighborDegree_value : neighborDegree = 500 := by
  norm_num [neighborDegree, h, Nat.choose]
@[simp] theorem n_value : n = 816 := by
  norm_num [n, v, h, Nat.choose]
@[simp] theorem m_value : m = 18 := by norm_num [m, h]
@[simp] theorem roleCount_value : roleCount = 409650 := by
  norm_num [roleCount, n, v, neighborDegree, h, Nat.choose]
@[simp] theorem batchSize_value : batchSize = 524288 := by
  norm_num [batchSize]
@[simp] theorem centerLoss_value : centerLoss = 324 := by
  norm_num [centerLoss, h]
@[simp] theorem deficit_value : deficit = 168 := by
  norm_num [deficit, n, centerLoss, v, h, Nat.choose]
@[simp] theorem residualBudget_value : residualBudget = 7373532 := by
  norm_num [residualBudget, roleCount, n, v, neighborDegree, h,
    deficit, centerLoss, Nat.choose]

theorem batch_bounds : 2 ^ 18 < roleCount ∧ roleCount ≤ batchSize := by
  norm_num [roleCount, batchSize, n, v, neighborDegree, h, Nat.choose]

theorem residual_identity : roleCount * m - residualBudget = deficit := by
  norm_num [residualBudget]

@[simp] theorem lambda_value : lambda = 1179627 / 65536 := by
  norm_num [lambda, m, deficit, batchSize, n, centerLoss, v, h, Nat.choose]

@[simp] theorem epsilon_value : epsilon = 7 / 393216 := by
  norm_num [epsilon, deficit, m, batchSize, n, centerLoss, v, h,
    Nat.choose]

theorem deficit_pos : 0 < deficit := by
  norm_num [deficit, n, centerLoss, v, h, Nat.choose]

end Parameters

/- The accounting formula is stated over integers to make the subtraction
   transparent.  The three terms correspond to the source/sink telescope,
   twice the central frame decreases, and one terminal Y-bank lift per role. -/
def accountingResidual (W m N h : ℤ) : ℤ :=
  W * m - 2 * N + 2 * (h * h) + N

def accountingDeficit (W m N h : ℤ) : ℤ :=
  W * m - accountingResidual W m N h

theorem accountingDeficit_formula (W m N h : ℤ) :
    accountingDeficit W m N h = N - 2 * (h * h) := by
  dsimp [accountingDeficit, accountingResidual]
  ring

theorem h18_accounting_deficit :
    accountingDeficit Parameters.roleCount Parameters.m Parameters.n
      Parameters.h = 168 := by
  norm_num [accountingDeficit, accountingResidual, Parameters.roleCount,
    Parameters.m, Parameters.n, Parameters.h, Parameters.v,
    Parameters.neighborDegree, Nat.choose]

end H18OneStageCandidate
end ExactFourier
end OAI
