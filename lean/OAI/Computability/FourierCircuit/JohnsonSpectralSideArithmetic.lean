import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# H=24 Johnson-spectral side-bank arithmetic

The Johnson decomposition of the diagonal-free side matrix has harmonic
dimensions `1,23,252,1748`; the degree 0 and 1 terms can be folded into the
existing 24 centre coordinates, leaving a rank-2000 high block.  This file
records its exact width and the conditional full-frame charge caused by the
dense spectral projection rows.  The spectral eigenvalue and binary-span
lemmas are separate mathematical obligations.
-/

namespace OAI
namespace ExactFourier
namespace JohnsonSpectralSideArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m
def highRank : ℕ := 252 + 1748
def roleCount : ℕ := 2 * N0 + I0 * (highRank + h)
def padding : ℕ := 2 ^ 36
def saving : ℕ := CenterCompression.H24.deltaCompressed
def denseFramePenalty : ℕ := 2 * I0 * v
def margin : ℤ := (saving : ℤ) - (denseFramePenalty : ℤ)
def normalizedSaving : ℚ := (saving : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem highRank_eq : highRank = 2000 := by norm_num [highRank]
theorem roleCount_eq : roleCount = 41457349120 := by
  norm_num [roleCount, highRank, h, v, N0, I0,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]
theorem padding_eq : padding = 68719476736 := by norm_num [padding]
theorem padding_bounds : 2 ^ 35 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, highRank, h, v, N0, I0, padding,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]
theorem saving_eq : saving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq
theorem denseFramePenalty_eq : denseFramePenalty = 49748818944 := by
  norm_num [denseFramePenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]
theorem margin_eq : margin = -47323645952 := by
  norm_num [margin, saving_eq, denseFramePenalty_eq]
theorem margin_negative : margin < 0 := by
  rw [margin_eq]
  norm_num
theorem normalizedSaving_eq :
    normalizedSaving = 2368333 / 927712935936 := by
  norm_num [normalizedSaving, saving_eq, padding_eq,
    m, CenterCompression.H24.m, CenterCompression.H24.h]

end H24
end JohnsonSpectralSideArithmetic
end ExactFourier
end OAI
