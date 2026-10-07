import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Arithmetic for the source-indexed side-bank candidate

The scalar map `V x = x` with the existing `sideAction` readout uses one
auxiliary coordinate per source triple.  This file records its nominal
width and the exact h = 24 padding comparison.  It does not assert that the
source-indexed bank is compatible with the existing row-5 frame boundary;
that conditional audit is recorded separately in the repository notes.
-/

namespace OAI
namespace ExactFourier
namespace SourceIndexedSideArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m

/- Two source/target banks, one source-indexed side bank, and h centre lines. -/
def roleCount : ℕ := 2 * N0 + I0 * (v + h)
def padding : ℕ := 2 ^ 36
def centreSaving : ℕ := 2 * N0 - 2 * I0 * h ^ 2
def effectiveSaving : ℤ := (centreSaving : ℤ)
def normalizedSaving : ℚ :=
  (centreSaving : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem v_eq : v = 2024 := by
  norm_num [v, h, CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem N0_eq : N0 = 8291469824 := by
  norm_num [N0, v, h, CenterCompression.H24.N0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem I0_eq : I0 = 12289728 := by
  norm_num [I0, v, h, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem m_eq : m = 13824 := by
  norm_num [m, CenterCompression.H24.m, CenterCompression.H24.h]

theorem roleCount_eq : roleCount = 41752302592 := by
  norm_num [roleCount, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 68719476736 := by
  norm_num [padding]

theorem padding_bounds : 2 ^ 35 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, padding, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  norm_num [centreSaving, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem effectiveSaving_eq : effectiveSaving = 2425172992 := by
  change (centreSaving : ℤ) = 2425172992
  rw [centreSaving_eq]
  norm_num

theorem normalizedSaving_eq :
    normalizedSaving = 2368333 / 927712935936 := by
  norm_num [normalizedSaving, centreSaving, padding, m, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h,
    CenterCompression.H24.m, Nat.choose]

end H24
end SourceIndexedSideArithmetic
end ExactFourier
end OAI
