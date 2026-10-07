import OAI.Computability.FourierCircuit.SideMomentArithmetic
import Mathlib.Tactic.NormNum

/-!
# Conditional frame-cost obstruction for the moment candidate

The moment factorization is a scalar identity.  If its `h+1` aggregate moment
wires are instead forced through a full `m`-dimensional frame once per
invocation, the resulting directional penalty is already larger than the H=24
saving.  This is a conditional arithmetic warning: a successful frame design
must use nested low-dimensional labels rather than a full-frame transport.
-/

namespace OAI
namespace ExactFourier
namespace SideMomentFrameObstruction
namespace H24

open SideMomentArithmetic.H24

def momentPenalty : ℕ := 2 * I0 * (h + 1) * m

theorem momentPenalty_eq : momentPenalty = 8494659993600 := by
  norm_num [momentPenalty, I0, h, m,
    SideMomentArithmetic.H24.I0,
    SideMomentArithmetic.H24.h,
    SideMomentArithmetic.H24.m,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.m,
    CenterCompression.H24.v,
    Nat.choose]


def varyingFramePenalty : ℕ := 2 * I0 * (h + 1) * h

theorem varyingFramePenalty_eq : varyingFramePenalty = 14747673600 := by
  norm_num [varyingFramePenalty, I0, h,
    SideMomentArithmetic.H24.I0,
    SideMomentArithmetic.H24.h,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.v,
    Nat.choose]

theorem varyingFramePenalty_exceeds_saving :
    SideMomentArithmetic.H24.deltaMoment ≤ varyingFramePenalty := by
  norm_num [varyingFramePenalty, SideMomentArithmetic.H24.deltaMoment,
    I0, h, N0,
    SideMomentArithmetic.H24.I0,
    SideMomentArithmetic.H24.h,
    SideMomentArithmetic.H24.N0,
    SideMomentArithmetic.H24.v,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.N0,
    CenterCompression.H24.v,
    Nat.choose]

theorem momentPenalty_exceeds_saving :
    SideMomentArithmetic.H24.deltaMoment ≤ momentPenalty := by
  norm_num [momentPenalty, SideMomentArithmetic.H24.deltaMoment,
    I0, h, m, N0,
    SideMomentArithmetic.H24.I0,
    SideMomentArithmetic.H24.h,
    SideMomentArithmetic.H24.m,
    SideMomentArithmetic.H24.N0,
    SideMomentArithmetic.H24.v,
    CenterCompression.H24.I0,
    CenterCompression.H24.h,
    CenterCompression.H24.m,
    CenterCompression.H24.N0,
    CenterCompression.H24.v,
    Nat.choose]

theorem full_frame_margin_zero (extra : ℕ)
    (hextra : momentPenalty ≤ extra) :
    SideMomentArithmetic.H24.deltaMoment - extra = 0 := by
  apply Nat.sub_eq_zero_of_le
  exact le_trans momentPenalty_exceeds_saving hextra

end H24
end SideMomentFrameObstruction
end ExactFourier
end OAI
