import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Arithmetic obstruction for target-aggregated side roles

The scalar target aggregate uses `v` roles per invocation.  A common full
row-2/row-5 frame compatible with the existing stage boundary requires two
extra residual dimensions per aggregate.  This file records the resulting
negative margin; it is independent of the shared frame formalization.
-/

namespace OAI
namespace ExactFourier
namespace TargetSideAggregate
namespace H24

open OAI.ExactFourier.CenterCompression

def Wtarget : ℕ := 2 * CenterCompression.H24.N0 + CenterCompression.H24.I0 * (CenterCompression.H24.v + CenterCompression.H24.h)
def delta0 : ℕ := CenterCompression.H24.deltaCompressed
def boundaryPenalty : ℕ := 2 * CenterCompression.H24.I0 * CenterCompression.H24.v
def effectiveDelta : ℤ :=
  (delta0 : ℤ) - (boundaryPenalty : ℤ)

theorem Wtarget_eq : Wtarget = 41752302592 := by
  norm_num [Wtarget, CenterCompression.H24.N0, CenterCompression.H24.I0, CenterCompression.H24.v, CenterCompression.H24.h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem boundaryPenalty_eq : boundaryPenalty = 49748818944 := by
  norm_num [boundaryPenalty, CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem delta0_eq : delta0 = 2425172992 := by
  norm_num [delta0, CenterCompression.H24.deltaCompressed, CenterCompression.H24.N0, CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem effectiveDelta_eq : effectiveDelta = -47323645952 := by
  norm_num [effectiveDelta, delta0, boundaryPenalty,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.N0, CenterCompression.H24.I0, CenterCompression.H24.v, CenterCompression.H24.h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem effectiveDelta_nonpositive : effectiveDelta ≤ 0 := by
  rw [effectiveDelta_eq]
  norm_num

end H24
end TargetSideAggregate
end ExactFourier
end OAI
