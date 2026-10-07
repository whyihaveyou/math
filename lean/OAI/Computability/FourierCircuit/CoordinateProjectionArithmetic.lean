import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# h = 24 arithmetic for the rank-h coordinate projection candidate

The scalar candidate keeps h selected triple coordinates in the centre bank and
puts the v-h remaining coordinates in a diagonal residual side bank.  This
file records the exact widths and the conditional row-boundary charge.  The
frame obstruction itself is documented in `docs/coordinate-projection-frame-audit.md`:
current side roles exclude diagonal source/target pairs.
-/

namespace OAI
namespace ExactFourier
namespace CoordinateProjectionArithmetic
namespace H24

open OAI.ExactFourier.CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m

def sideRoles : ℕ := v - h
def centerRoles : ℕ := h
def roleCount : ℕ := 2 * N0 + I0 * (sideRoles + centerRoles)
def padding : ℕ := 2 ^ 36

def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def conditionalPenalty : ℕ := 2 * I0 * sideRoles
def conditionalMargin : ℤ := (centreSaving : ℤ) - (conditionalPenalty : ℤ)
def conditionalNormalizedMargin : ℚ :=
  (conditionalMargin : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem h_eq : h = 24 := by
  rfl

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem sideRoles_eq : sideRoles = 2000 := by
  norm_num [sideRoles, v, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centerRoles_eq : centerRoles = 24 := by
  rfl

theorem roleCount_eq : roleCount = 41457349120 := by
  norm_num [roleCount, sideRoles, centerRoles, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 68719476736 := by
  norm_num [padding]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem conditionalPenalty_eq : conditionalPenalty = 49158912000 := by
  norm_num [conditionalPenalty, I0, sideRoles, v, h,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem conditionalMargin_eq : conditionalMargin = -46733739008 := by
  norm_num [conditionalMargin, centreSaving, conditionalPenalty,
    CenterCompression.H24.deltaCompressed, conditionalPenalty, I0,
    sideRoles, v, h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem conditionalMargin_neg : conditionalMargin < 0 := by
  rw [conditionalMargin_eq]
  norm_num

theorem conditionalNormalizedMargin_eq :
    conditionalNormalizedMargin = -45638417 / 927712935936 := by
  norm_num [conditionalNormalizedMargin, conditionalMargin_eq,
    m, padding, CenterCompression.H24.m, CenterCompression.H24.h]

theorem conditionalNormalizedMargin_neg : conditionalNormalizedMargin < 0 := by
  rw [conditionalNormalizedMargin_eq]
  norm_num

end H24
end CoordinateProjectionArithmetic
end ExactFourier
end OAI
