import OAI.Computability.FourierCircuit.CenterCompression

/-!
# Directional-budget interface for the centre-compressed frame audit

The paper's frame proof has two separate ingredients: signed dimension changes
telescope from source to sink, while every internal decrease is counted twice
when edge costs are replaced by absolute residual dimensions.  This file
records that accounting as a small arithmetic interface.  The hypotheses are
deliberately explicit: a future binary-subspace formalization must discharge
them from the labelled rows, rather than getting the saving from an arithmetic
definition alone.
-/

namespace OAI
namespace ExactFourier
namespace FrameBudget

def residualTotal (W m N I h : ℕ) : ℕ :=
  W * m - 2 * N + 2 * (I * h * h)

def saving (W m N I h : ℕ) : ℕ :=
  W * m - residualTotal W m N I h

theorem saving_formula
    (W m N I h : ℕ)
    (hbase : 2 * N ≤ W * m)
    (hloss : 2 * (I * h * h) ≤ 2 * N) :
    saving W m N I h = 2 * N - 2 * (I * h * h) := by
  have hsub : W * m - 2 * N + 2 * (I * h * h) ≤ W * m := by
    calc
      W * m - 2 * N + 2 * (I * h * h) ≤ W * m - 2 * N + 2 * N :=
        Nat.add_le_add_left hloss _
      _ = W * m := Nat.sub_add_cancel hbase
  rw [saving, residualTotal, Nat.sub_eq_iff_eq_add' hsub]
  calc
    W * m = (W * m - 2 * N) + 2 * N :=
      (Nat.sub_add_cancel hbase).symm
    _ = (W * m - 2 * N) +
        (2 * (I * h * h) + (2 * N - 2 * (I * h * h))) := by
      rw [Nat.add_sub_of_le hloss]
    _ = (W * m - 2 * N + 2 * (I * h * h)) +
        (2 * N - 2 * (I * h * h)) := by ac_rfl

theorem residual_nonnegative
    (W m N I h : ℕ) :
    0 ≤ residualTotal W m N I h := by
  exact Nat.zero_le _

namespace H24

def W : ℕ := CenterCompression.H24.Wcompressed
def m : ℕ := CenterCompression.H24.m
def N : ℕ := CenterCompression.H24.N0
def I : ℕ := CenterCompression.H24.I0
def h : ℕ := CenterCompression.H24.h
def residual : ℕ := residualTotal W m N I h
def delta : ℕ := saving W m N I h

theorem residual_eq : residual = 479235641870830592 := by
  norm_num [residual, residualTotal, W, m, N, I, h,
    CenterCompression.H24.Wcompressed,
    CenterCompression.H24.m,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    Nat.choose]

theorem delta_eq : delta = 2425172992 := by
  norm_num [delta, saving, residualTotal, W, m, N, I, h,
    CenterCompression.H24.Wcompressed,
    CenterCompression.H24.m,
    CenterCompression.H24.N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    Nat.choose]

 theorem delta_formula : delta = 2 * N - 2 * (I * h * h) := by
  apply saving_formula
  · norm_num [W, m, N, I, h, CenterCompression.H24.Wcompressed,
      CenterCompression.H24.m, CenterCompression.H24.N0,
      CenterCompression.H24.I0, CenterCompression.H24.h,
      CenterCompression.H24.v, CenterCompression.H24.dNbr, Nat.choose]
  · norm_num [W, m, N, I, h, CenterCompression.H24.Wcompressed,
      CenterCompression.H24.m, CenterCompression.H24.N0,
      CenterCompression.H24.I0, CenterCompression.H24.h,
      CenterCompression.H24.v, CenterCompression.H24.dNbr, Nat.choose]

end H24
end FrameBudget
end ExactFourier
end OAI
