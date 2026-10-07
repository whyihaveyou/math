import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Arithmetic for the direct diagonal frame obstruction

The pair/complement scalar interface reuses the source bank for `x_S`, so it
does not increase scalar width.  Under the existing row-5 common-frame rule,
the source line `t_S` and the target side frame `t_S^⊥` require one rise and
one return per target/invocation.  This file records that conditional charge.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementDirectFrameArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def saving : ℕ := CenterCompression.H24.deltaCompressed
def directFramePenalty : ℕ := 2 * I0 * v
def margin : ℤ := (saving : ℤ) - (directFramePenalty : ℤ)

theorem directFramePenalty_eq : directFramePenalty = 49748818944 := by
  norm_num [directFramePenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem saving_eq : saving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem margin_eq : margin = -47323645952 := by
  norm_num [margin, saving_eq, directFramePenalty_eq]

theorem margin_negative : margin < 0 := by
  rw [margin_eq]
  norm_num

end H24
end PairComplementDirectFrameArithmetic
end ExactFourier
end OAI
