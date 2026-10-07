import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for a pair-prefix side hierarchy

This is a conditional obstruction for one concrete local side-compression
hierarchy.  For a fixed pair `F = {i,j}`, the indicators
`e_i + e_j + e_k` (`k ∉ F`) are linearly independent, so their span has
dimension `h - 2` and codimension two in the active `h`-factor.  Under the
current three-stage labels, stages 2 and 3 require a pair aggregate to leave
that span and return if it is touched in the full active frame.  The optimistic
two-way cost is therefore four residual units per pair aggregate.  At H=24
the exact penalty is 9,045,239,808, larger than the centre-compressed saving
2,425,172,992.  This remains a conditional audit of this hierarchy; it does
not give a lower bound for arbitrary side-wire networks.
-/

namespace OAI
namespace ExactFourier
namespace SideHierarchyArithmetic
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def invocationsPerStage : ℕ := v ^ 2
def pairCount : ℕ := Nat.choose h 2
def stagesWithPriorLine : ℕ := 2
def pairCodimension : ℕ := h - (h - 2)
def twoWayCost : ℕ := 2 * pairCodimension
def pairBoundaryPenalty : ℕ :=
  stagesWithPriorLine * invocationsPerStage * pairCount * twoWayCost

theorem pairCount_eq : pairCount = 276 := by
  norm_num [pairCount, h, CenterCompression.H24.h, Nat.choose]

theorem invocationsPerStage_eq : invocationsPerStage = 4096576 := by
  norm_num [invocationsPerStage, v, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem pairCodimension_eq : pairCodimension = 2 := by
  norm_num [pairCodimension, h, CenterCompression.H24.h]

theorem twoWayCost_eq : twoWayCost = 4 := by
  norm_num [twoWayCost, pairCodimension, h, CenterCompression.H24.h]

theorem pairBoundaryPenalty_eq : pairBoundaryPenalty = 9045239808 := by
  norm_num [pairBoundaryPenalty, stagesWithPriorLine,
    invocationsPerStage, pairCount, twoWayCost, pairCodimension,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v,
    Nat.choose]

theorem pairBoundaryPenalty_exceeds_saving :
    CenterCompression.H24.deltaCompressed ≤ pairBoundaryPenalty := by
  norm_num [pairBoundaryPenalty, stagesWithPriorLine,
    invocationsPerStage, pairCount, twoWayCost, pairCodimension,
    CenterCompression.H24.deltaCompressed,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    h, v, CenterCompression.H24.h, CenterCompression.H24.v,
    Nat.choose]

theorem residual_margin_nonpositive (extra : ℕ)
    (hextra : pairBoundaryPenalty ≤ extra) :
    CenterCompression.H24.deltaCompressed - extra = 0 := by
  apply Nat.sub_eq_zero_of_le
  exact le_trans pairBoundaryPenalty_exceeds_saving hextra

end H24
end SideHierarchyArithmetic
end ExactFourier
end OAI
