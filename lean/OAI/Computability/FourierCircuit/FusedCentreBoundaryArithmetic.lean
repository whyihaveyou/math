import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Conditional arithmetic for fusing one centre boundary

The current h=24 ledger loses `2 * I₀ * h^2`, with `I₀ = 3 v^2`.
If a redesigned gate algebra fuses one of the three centre decreases, the
remaining loss would be `4 * v^2 * h^2`.  This file verifies the resulting
integer and rational ledger only.  It does not assert the required fused
frame schedule or arbitrary-bank restoration.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreBoundaryArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def m : ℕ := CenterCompression.H24.m
def Wstar : ℕ := CenterCompression.H24.Wstar

def fusedSaving : ℕ := 2 * N0 - 4 * v ^ 2 * h ^ 2
def normalized : ℚ := (fusedSaving : ℚ) / ((m : ℚ) * Wstar)

theorem fusedSaving_eq : fusedSaving = 7144428544 := by
  norm_num [fusedSaving, N0, v, h, CenterCompression.H24.N0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem Wstar_eq : Wstar = 35184372088832 := by
  exact CenterCompression.H24.Wstar_eq

theorem m_eq : m = 13824 := by
  exact CenterCompression.H24.m_eq

theorem normalized_eq :
    normalized = 6976981 / 474989023199232 := by
  norm_num [normalized, fusedSaving_eq, Wstar_eq, m_eq]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

theorem normalized_gt_current :
    CenterCompression.H24.epsilonCompressed < normalized := by
  rw [CenterCompression.H24.epsilonCompressed_eq, normalized_eq]
  norm_num

end H24
end FusedCentreBoundaryArithmetic
end ExactFourier
end OAI
