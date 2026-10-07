import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# Conditional h = 18 fused-centre arithmetic

The h = 24 centre-boundary audit has a positive conditional ledger when one
centre boundary is fused.  This file repeats exactly that integer calculation
at h = 18, using the full published r = 3 role-count formula and its next
power-of-two padding.  It is an arithmetic stress test only: it does not
provide the h = 18 frame-labelled terminal interface, a legal fused gate, or
an all-length recursion.

The point of recording the candidate separately is that the same hypothetical
one-boundary fusion clears the 10^-9 scale by a larger margin at h = 18.  The
existing h = 18 terminal audit still shows that the standard common-frame
terminal bank cannot be used at the old one-stage price, so this certificate
must not be read as a completed exponent theorem.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreBoundaryArithmeticH18

def h : ℕ := 18
def v : ℕ := Nat.choose h 3
def d : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def N0 : ℕ := v ^ 3
def I0 : ℕ := 3 * v ^ 2
def roleCount : ℕ :=
  2 * N0 + I0 * (v * d + h + 1)
def Wstar : ℕ := 2 ^ 40
def m : ℕ := h ^ 3

/- The hypothetical one-boundary fusion removes one of the three h^2 centre
   losses.  The remaining loss is `4 v^2 h^2`. -/
def fusedSaving : ℕ := 2 * N0 - 4 * v ^ 2 * h ^ 2
def shearCharge : ℕ := I0 * h
def fusedMargin : ℤ := (fusedSaving : ℤ) - (shearCharge : ℤ)
def normalized : ℚ :=
  (fusedMargin : ℚ) / ((m : ℚ) * (Wstar : ℚ))

theorem h_eq : h = 18 := by rfl

theorem v_eq : v = 816 := by
  norm_num [v, h, Nat.choose]

theorem d_eq : d = 500 := by
  norm_num [d, h, Nat.choose]

theorem N0_eq : N0 = 543338496 := by
  norm_num [N0, v, h, Nat.choose]

theorem I0_eq : I0 = 1997568 := by
  norm_num [I0, v, h, Nat.choose]

theorem roleCount_eq : roleCount = 816132374784 := by
  norm_num [roleCount, N0, I0, v, d, h, Nat.choose]

theorem padding_bounds : 2 ^ 39 < roleCount ∧ roleCount ≤ Wstar := by
  norm_num [roleCount, Wstar, N0, I0, v, d, h, Nat.choose]

theorem Wstar_eq : Wstar = 1099511627776 := by
  norm_num [Wstar]

theorem m_eq : m = 5832 := by
  norm_num [m, h]

theorem fusedSaving_eq : fusedSaving = 223727616 := by
  norm_num [fusedSaving, N0, v, h, Nat.choose]

theorem shearCharge_eq : shearCharge = 35956224 := by
  norm_num [shearCharge, I0, v, h, Nat.choose]

theorem fusedMargin_eq : fusedMargin = 187771392 := by
  norm_num [fusedMargin, fusedSaving, shearCharge, N0, I0, v, h,
    Nat.choose]

theorem fusedMargin_pos : 0 < fusedMargin := by
  rw [fusedMargin_eq]
  norm_num

theorem normalized_eq :
    normalized = 13583 / 463856467968 := by
  norm_num [normalized, fusedMargin_eq, m_eq, Wstar_eq]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

end FusedCentreBoundaryArithmeticH18
end ExactFourier
end OAI
