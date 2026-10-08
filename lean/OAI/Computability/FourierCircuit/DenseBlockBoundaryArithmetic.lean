import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Conditional h=24 arithmetic for the dense two-frame block route

The dense labels `u = e₀` and `w = 1 + e₀` split targets into two blocks.  A
separate executable audit proves the exact binary common-boundary ranks.  This
file records only the associated conditional direction ledger: one two-unit
switch at each of the three prefix sizes.  The resulting normalized candidate
is above `10⁻⁹` under that explicit route premise.

No complex gate, scalar/gate commutation, global schedule, or all-length DFT
recurrence is proved here.
-/

namespace OAI
namespace ExactFourier
namespace DenseBlockBoundaryArithmetic

namespace H24

abbrev h : ℕ := CenterCompression.H24.h
abbrev m : ℕ := CenterCompression.H24.m
abbrev saving : ℕ := CenterCompression.H24.deltaCompressed
abbrev prefixSum : ℕ := 1 + h + h ^ 2
abbrev switchCharge : ℕ := 2 * prefixSum

def blockMargin : ℤ := (saving : ℤ) - (switchCharge : ℤ)
def normalized : ℚ :=
  blockMargin / ((m : ℚ) * (CenterCompression.H24.Wstar : ℚ))

theorem h_eq : h = 24 := by rfl

theorem m_eq : m = 13824 := by
  exact CenterCompression.H24.m_eq

theorem saving_eq : saving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem prefixSum_eq : prefixSum = 601 := by
  norm_num [prefixSum, h, CenterCompression.H24.h]

theorem switchCharge_eq : switchCharge = 1202 := by
  rw [switchCharge, prefixSum_eq]

theorem blockMargin_eq : blockMargin = 2425171790 := by
  rw [blockMargin, saving_eq, switchCharge_eq]
  norm_num

theorem normalized_eq :
    normalized = 1212585895 / 243194379878006784 := by
  rw [normalized, blockMargin_eq, m_eq,
    CenterCompression.H24.Wstar_eq]
  norm_num

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

end H24
end DenseBlockBoundaryArithmetic
end ExactFourier
end OAI
