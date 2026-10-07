import Mathlib.Tactic.NormNum
import OAI.Computability.FourierCircuit.CenterCompression

/-!
# Conditional arithmetic obstruction to side-wire grouping

Grouping two incomparable source or target labels requires a join and a later
removal in a nested-frame implementation.  If each extra neighbour incidence
therefore costs two directional residual units, the resulting penalty can be
checked independently of the detailed frame construction.  This file proves
the exact H=24 arithmetic.  The geometric premise itself remains a research
obligation for any proposed grouping scheme.
-/

namespace OAI
namespace ExactFourier
namespace SideMergeObstruction

namespace H24

def v : ℕ := CenterCompression.H24.v
def dNbr : ℕ := CenterCompression.H24.dNbr
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0

/- Two residual units for each extra neighbour incidence. -/
def mergePenalty : ℕ := 2 * I0 * v * (dNbr - 1)

theorem mergePenalty_eq : mergePenalty = 69250355970048 := by
  norm_num [mergePenalty, I0, v, dNbr, N0,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.N0,
    CenterCompression.H24.h,
    Nat.choose]

theorem base_margin_eq : 2 * N0 = 16582939648 := by
  norm_num [N0, CenterCompression.H24.N0,
    CenterCompression.H24.v,
    CenterCompression.H24.h,
    Nat.choose]

theorem mergePenalty_eq_multiple_margin :
    mergePenalty = 4176 * (2 * N0) := by
  norm_num [mergePenalty, N0, I0, v, dNbr,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.N0,
    CenterCompression.H24.h,
    Nat.choose]

theorem mergePenalty_exceeds_margin : 2 * N0 ≤ mergePenalty := by
  norm_num [mergePenalty, N0, I0, v, dNbr,
    CenterCompression.H24.I0,
    CenterCompression.H24.v,
    CenterCompression.H24.dNbr,
    CenterCompression.H24.N0,
    CenterCompression.H24.h,
    Nat.choose]

/- If a proposed grouping really incurs this penalty, no positive saving can
   remain, even before charging the centre wires. -/
theorem revised_margin_zero (extra : ℕ) (hextra : mergePenalty ≤ extra) :
    2 * N0 - extra = 0 := by
  apply Nat.sub_eq_zero_of_le
  exact le_trans mergePenalty_exceeds_margin hextra

end H24
end SideMergeObstruction
end ExactFourier
end OAI
