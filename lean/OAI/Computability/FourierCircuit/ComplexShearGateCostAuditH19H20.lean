import OAI.Computability.FourierCircuit.FusedCentreBoundaryArithmeticH19H20
import OAI.Computability.FourierCircuit.ComplexShearGateBridge
import Mathlib.Tactic.NormNum

/-!
# Route-specific two-gate cost stress test at h = 19 and h = 20

`ComplexShearGateBridge` realizes one matrix-level complex transvection by two
scalar gates.  If the six-phase fused ledger instantiates every charged
 directional unit with that concrete two-gate realization, its shear term is
`12 * shearCharge` rather than `6 * shearCharge`.  The resulting numbers are
recorded here as a conservative audit of that particular route.

This is not a lower bound for all scalar circuits: a different realization may
use a primitive transvection, a free wire permutation, or a different schedule.
It is also not a frame-compatibility theorem.  It only prevents the existing
h19/h20 arithmetic certificate from being presented as a proved scalar-gate
saving under this explicit two-gate instantiation.
-/

namespace OAI
namespace ExactFourier
namespace ComplexShearGateCostAuditH19H20

open FusedCentreBoundaryArithmeticH19H20

/-- Margin after charging two scalar gates for each directional unit in all six
phases. -/
def twoGateMargin (h : ℕ) : ℤ :=
  (fusedSaving h : ℤ) - 12 * (shearCharge h : ℤ)

def normalized (h padding : ℕ) : ℚ :=
  (twoGateMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

theorem twoGateMargin19_eq : twoGateMargin 19 = -178402590 := by
  norm_num [twoGateMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem twoGateMargin20_eq : twoGateMargin 20 = -51984000 := by
  norm_num [twoGateMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem normalized19_eq :
    normalized 19 padding19 = -13005 / 1099511627776 := by
  norm_num [normalized, padding19, twoGateMargin, fusedSaving,
    shearCharge, baseCount, incidenceCount, value, Nat.choose]

theorem normalized20_eq :
    normalized 20 padding20 = -3249 / 2199023255552 := by
  norm_num [normalized, padding20, twoGateMargin, fusedSaving,
    shearCharge, baseCount, incidenceCount, value, Nat.choose]

theorem normalized19_lt_zero : normalized 19 padding19 < 0 := by
  rw [normalized19_eq]
  norm_num

theorem normalized20_lt_zero : normalized 20 padding20 < 0 := by
  rw [normalized20_eq]
  norm_num

end ComplexShearGateCostAuditH19H20
end ExactFourier
end OAI
