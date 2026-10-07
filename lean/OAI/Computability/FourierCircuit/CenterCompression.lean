import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic certificate for removing the global centre wire

The exact construction uses three-element source and target triples.  If
`q` denotes the global sum, replace the `h + 1` centre coordinates by

    c'_i = c_i - q / 3.

For a target triple `S`, the readout is then half the sum of its three
coordinates.  This file proves the scalar identity behind that replacement
and checks the resulting `h = 24` arithmetic.  It does not formalize the
frame-labelled circuit itself.
-/

namespace OAI
namespace ExactFourier
namespace CenterCompression

theorem three_point_shift
    {α K : Type*} [Field K] [CharZero K]
    (S : Finset α) (hS : S.card = 3)
    (g : α → K) (q : K) :
    (S.sum (fun i => g i - q / (3 : K))) / 2 =
      ((S.sum g) - q) / 2 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp [hS]
  field_simp

/- The two maps used by the compressed centre bank. -/
theorem compressed_entry
    {α K : Type*} [Field K] [CharZero K]
    (S : Finset α) (hS : S.card = 3)
    (g : α → K) (q : K) :
    ((S.sum (fun i => g i - q / (3 : K))) / 2) =
      (S.sum g - q) / 2 := by
  exact three_point_shift S hS g q

theorem incidence_sum
    {α K : Type*} [Field K] [CharZero K] [DecidableEq α]
    (S T : Finset α) :
    S.sum (fun i => if i ∈ T then (1 : K) else 0) =
      (S ∩ T).card := by
  rw [← Finset.filter_mem_eq_inter]
  rw [← Finset.sum_filter]
  simp

theorem compressed_triple_entry
    {α K : Type*} [Field K] [CharZero K] [DecidableEq α]
    (S T : Finset α) (hS : S.card = 3) :
    (S.sum (fun i =>
      (if i ∈ T then (1 : K) else 0) - (1 : K) / 3)) / 2 =
        ((S ∩ T).card - 1 : K) / 2 := by
  rw [three_point_shift S hS (fun i => if i ∈ T then (1 : K) else 0) 1]
  rw [incidence_sum]

namespace H24

def h : ℕ := 24
def v : ℕ := Nat.choose h 3
def dNbr : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def N0 : ℕ := v ^ 3
def I0 : ℕ := 3 * v ^ 2
def m : ℕ := h ^ 3

/- The `c_*` coordinate has been absorbed into the h shifted centres. -/
def Wcompressed : ℕ := 2 * N0 + I0 * (v * dNbr + h)
def Wstar : ℕ := 2 ^ 45
def deltaCompressed : ℕ := 2 * N0 - 2 * I0 * h ^ 2
def epsilonCompressed : ℚ :=
  (deltaCompressed : ℚ) / ((m : ℚ) * (Wstar : ℚ))

theorem v_eq : v = 2024 := by
  norm_num [Nat.choose, v, h]

theorem dNbr_eq : dNbr = 1393 := by
  norm_num [Nat.choose, dNbr, h]

theorem N0_eq : N0 = 8291469824 := by
  norm_num [N0, v, h, Nat.choose]

theorem I0_eq : I0 = 12289728 := by
  norm_num [I0, v, h, Nat.choose]

theorem m_eq : m = 13824 := by
  norm_num [m, h]

theorem Wcompressed_eq : Wcompressed = 34666930287616 := by
  norm_num [Wcompressed, N0, I0, v, dNbr, h, Nat.choose]

theorem Wstar_eq : Wstar = 35184372088832 := by
  norm_num [Wstar]

theorem deltaCompressed_eq : deltaCompressed = 2425172992 := by
  norm_num [deltaCompressed, N0, I0, v, h, Nat.choose]

theorem epsilonCompressed_eq :
    epsilonCompressed = 2368333 / 474989023199232 := by
  norm_num [epsilonCompressed, deltaCompressed, m, Wstar, N0, I0, v, h,
    Nat.choose]

end H24
end CenterCompression
end ExactFourier
end OAI
