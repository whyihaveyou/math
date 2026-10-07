import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Arithmetic certificate for the pair/complement side candidate

This file records exact h=24 arithmetic for the pair/complement scalar
factorization.  It deliberately does not claim that the scalar maps have
been inserted into the eight-row framed circuit.  The accompanying note and
Python script contain the conditional frame audit.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementSideArithmetic

namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m
def pairCount : ℕ := Nat.choose h 2

/-- Two pair banks, plus the existing h centre wires. -/
def roleCount : ℕ := 2 * N0 + I0 * (2 * pairCount + h)
def padding : ℕ := 2 ^ 35
def delta : ℕ := CenterCompression.H24.deltaCompressed
def normalized : ℚ := (delta : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem pairCount_eq : pairCount = 276 := by
  norm_num [pairCount, h, CenterCompression.H24.h, Nat.choose]

theorem roleCount_eq : roleCount = 23661822976 := by
  norm_num [roleCount, pairCount, h, N0, I0,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 34359738368 := by
  norm_num [padding]

theorem delta_eq : delta = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem normalized_eq :
    normalized = 2368333 / 463856467968 := by
  norm_num [normalized, delta_eq, padding_eq, m,
    CenterCompression.H24.m_eq]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

theorem normalized_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < normalized := by
  rw [normalized_eq]
  norm_num

/-- For r=0,1,2,3 the two pair counts give the diagonal-free coefficient.
    Here h-6=18, so the difference is divided by 36 and the global coefficient
    is 19/4. -/
def pairCoefficient (r : Fin 4) : ℚ :=
  ((Nat.choose r.val 2 : ℚ) -
      (Nat.choose (18 + r.val) 2 : ℚ)) / 36 + 19 / 4

theorem pairCoefficient_eq_sideCoefficient (r : Fin 4) :
    pairCoefficient r = (1 - (r.val : ℚ)) / 2 := by
  fin_cases r <;> norm_num [pairCoefficient, Nat.choose]

end H24

end PairComplementSideArithmetic
end ExactFourier
end OAI

