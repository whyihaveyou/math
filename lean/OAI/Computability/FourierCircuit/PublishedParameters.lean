import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

namespace OAI
namespace ExactFourier
namespace ExplicitParameters

/-!
# Published finite-network constants (h = 100)

This file checks, by exact arithmetic, the numerical constants displayed in
Section 2 of *An explicit power-saving for the exact discrete Fourier
transform*.  It is deliberately only an arithmetic certificate: it does not
formalize the binary-frame network, the recursive algorithm, or its running
time bound.
-/

def h : ℕ := 100
def v : ℕ := Nat.choose h 3
def neighborDegree : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def n0 : ℕ := v ^ 3
def i0 : ℕ := 3 * v ^ 2
def m : ℕ := h ^ 3
def roleCount : ℕ := 2 * n0 + i0 * (v * neighborDegree + h + 1)
def roleCountPadded : ℕ := 2 ^ 71
def delta : ℕ := 2 * v ^ 2 * (v - 3 * h * (h + 1))
def directionalCount : ℕ := roleCount * m - delta
def epsilon : ℚ := (delta : ℚ) / (m * roleCountPadded)
def lambda : ℚ := (m : ℚ) - (delta : ℚ) / roleCountPadded

/-- These two helper facts keep the larger certificates fast to elaborate. -/
theorem choose_100_3 : Nat.choose 100 3 = 161700 := by decide
theorem choose_97_3 : Nat.choose 97 3 = 147440 := by decide

@[simp] theorem h_value : h = 100 := by rfl
@[simp] theorem v_value : v = 161700 := by
  norm_num [v, h, choose_100_3]
@[simp] theorem neighborDegree_value : neighborDegree = 147731 := by
  norm_num [neighborDegree, h, choose_97_3]
@[simp] theorem n0_value : n0 = 4227952113000000 := by
  norm_num [n0, v, h, choose_100_3]
@[simp] theorem i0_value : i0 = 78440670000 := by
  norm_num [i0, v, h, choose_100_3]
@[simp] theorem m_value : m = 1000000 := by
  norm_num [m, h]
@[simp] theorem roleCount_value : roleCount = 1873807244643542670000 := by
  norm_num [roleCount, n0, i0, v, neighborDegree, h, choose_100_3, choose_97_3]
@[simp] theorem roleCountPadded_value : roleCountPadded = 2361183241434822606848 := by
  norm_num [roleCountPadded]
@[simp] theorem delta_value : delta = 6871402692000000 := by
  norm_num [delta, v, h, choose_100_3]
@[simp] theorem directionalCount_value :
    directionalCount = 1873807244636671267308000000 := by
  norm_num [directionalCount, roleCount, n0, i0, v, neighborDegree, h, m, delta,
    choose_100_3, choose_97_3]

/- The published role count is between 2^70 and 2^71, so 2^71 is the next
power-of-two batch size. -/
theorem roleCount_bounds :
    2 ^ 70 < roleCount ∧ roleCount ≤ roleCountPadded := by
  norm_num [roleCount, n0, i0, v, neighborDegree, h, roleCountPadded,
    choose_100_3, choose_97_3]

theorem delta_pos : 0 < delta := by
  norm_num [delta, v, h, choose_100_3]

@[simp] theorem epsilon_value :
    epsilon = 1717850673 / 590295810358705651712 := by
  norm_num [epsilon, delta, m, roleCountPadded, v, h, choose_100_3]

@[simp] theorem lambda_value :
    lambda = 9223372036827934391234375 / 9223372036854775808 := by
  norm_num [lambda, delta, m, roleCountPadded, v, h, choose_100_3]

theorem epsilon_lower_bound : (28 : ℚ) / 10 ^ 13 < epsilon := by
  norm_num [epsilon, delta, m, roleCountPadded, v, h, choose_100_3]

theorem lambda_bounds : 1 < lambda ∧ lambda < m := by
  norm_num [lambda, delta, m, roleCountPadded, v, h, choose_100_3]

theorem block_dimension_even : Even m := by
  refine ⟨500000, by norm_num [m, h]⟩

end ExplicitParameters
end ExactFourier
end OAI
