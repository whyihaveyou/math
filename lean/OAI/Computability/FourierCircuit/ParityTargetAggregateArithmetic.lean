import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Conditional parity-projected target aggregate obstruction

For each target triple S, a single aggregate over all even-intersection source
triples has a row-5-compatible label inside t_S^perp.  If its source update
is made in a common row-2 gate with the other target aggregates, the prefix
component must be raised to the full active factor and then returned.  The
conditional two-direction charge is two units per target aggregate and
invocation.  This file records the exact h=24 arithmetic only; it is not a
universal lower bound for redesigned schedules.
-/

namespace OAI
namespace ExactFourier
namespace ParityTargetAggregateArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m
def delta : ℕ := CenterCompression.H24.deltaCompressed
def parityPenalty : ℕ := 2 * I0 * v
def effectiveDelta : ℤ := (delta : ℤ) - (parityPenalty : ℤ)

theorem parityPenalty_eq : parityPenalty = 49748818944 := by
  norm_num [parityPenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem delta_eq : delta = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem effectiveDelta_eq : effectiveDelta = -47323645952 := by
  rw [effectiveDelta, delta_eq, parityPenalty_eq]
  norm_num

theorem effectiveDelta_neg : effectiveDelta < 0 := by
  rw [effectiveDelta_eq]
  norm_num

theorem parityPenalty_exceeds_delta : delta < parityPenalty := by
  rw [delta_eq, parityPenalty_eq]
  norm_num

end H24
end ParityTargetAggregateArithmetic
end ExactFourier
end OAI
