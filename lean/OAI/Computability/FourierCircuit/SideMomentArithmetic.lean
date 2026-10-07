import OAI.Computability.FourierCircuit.CenterCompression

/-!
# Arithmetic for the moment-factorized side correction candidate

The scalar side identity in `SideMomentFactorization.lean` uses one global
moment and `h` incidence moments per invocation, plus the existing `h`
compressed centre coordinates.  This file counts that candidate only.  The
frame labels, the shared source-bank touch in the direct `x_S` term, and the
reversible eight-row schedule are not asserted here.
-/

namespace OAI
namespace ExactFourier
namespace SideMomentArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def dNbr : ℕ := CenterCompression.H24.dNbr
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m

def sideAux : ℕ := h + 1
def centerAux : ℕ := h
def Wmoment : ℕ := 2 * N0 + I0 * (sideAux + centerAux)
def Wstar : ℕ := 2 ^ 35
def deltaMoment : ℕ := 2 * N0 - 2 * I0 * h ^ 2
def sMoment : ℕ := Wmoment * m - deltaMoment
def epsilonMoment : ℚ :=
  (deltaMoment : ℚ) / ((m : ℚ) * (Wstar : ℚ))

theorem sideAux_eq : sideAux = 25 := by
  norm_num [sideAux, h, CenterCompression.H24.h]

theorem centerAux_eq : centerAux = 24 := by
  norm_num [centerAux, h, CenterCompression.H24.h]

theorem Wmoment_eq : Wmoment = 17185136320 := by
  norm_num [Wmoment, sideAux, centerAux, N0, I0, v, dNbr, h,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.h,
    Nat.choose]

theorem Wstar_eq : Wstar = 34359738368 := by
  norm_num [Wstar]

theorem Wstar_bounds : 2 ^ 34 < Wmoment ∧ Wmoment ≤ Wstar := by
  norm_num [Wmoment, Wstar, sideAux, centerAux, N0, I0, v, dNbr, h,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.h,
    Nat.choose]

theorem deltaMoment_eq : deltaMoment = 2425172992 := by
  norm_num [deltaMoment, N0, I0, v, h,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.h,
    Nat.choose]

theorem sMoment_eq : sMoment = 237564899314688 := by
  norm_num [sMoment, Wmoment, deltaMoment, sideAux, centerAux, N0, I0, v, dNbr, h, m,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.h,
    CenterCompression.H24.m,
    Nat.choose]

theorem epsilonMoment_eq :
    epsilonMoment = 2368333 / 463856467968 := by
  norm_num [epsilonMoment, deltaMoment, Wstar, m, N0, I0, v, h,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.h,
    CenterCompression.H24.m,
    Nat.choose]

end H24
end SideMomentArithmetic
end ExactFourier
end OAI
