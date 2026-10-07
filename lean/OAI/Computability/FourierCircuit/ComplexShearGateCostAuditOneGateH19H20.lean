import OAI.Computability.FourierCircuit.FusedCentreBoundaryArithmeticH19H20
import OAI.Computability.FourierCircuit.ComplexShearGateBridge
import Mathlib.Tactic.NormNum

/-!
# Unit-gate comparison for the h=19 and h=20 fused ledger

`oneGateUnitShear` realizes a coefficient-one complex transvection with one
scalar `Gate.add`.  If every directional unit in the six-phase ledger is
instantiated by this unit-coefficient route, the arithmetic is exactly the
primitive six-phase ledger.  The certificate is useful as a comparison point;
it still requires a proof that the binary frame transport can be represented
by these complex coordinate shears and scheduled globally.

The file therefore records a positive primitive-gate accounting result while
leaving the binary-frame-to-complex-coordinate map, frame preservation, bank
commutation, and all-length schedule as explicit open obligations.
-/

namespace OAI
namespace ExactFourier
namespace ComplexShearGateCostAuditOneGateH19H20

open FusedCentreBoundaryArithmeticH19H20

/-- Six-phase margin when one coefficient-one scalar add is charged per
 directional unit. -/
def oneGateMargin (h : ℕ) : ℤ :=
  (fusedSaving h : ℤ) - 6 * (shearCharge h : ℤ)

def normalized (h padding : ℕ) : ℚ :=
  (oneGateMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

theorem oneGateMargin19_eq : oneGateMargin 19 = 142722072 := by
  norm_num [oneGateMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem oneGateMargin20_eq : oneGateMargin 20 = 415872000 := by
  norm_num [oneGateMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem normalized19_eq :
    normalized 19 padding19 = 2601 / 274877906944 := by
  norm_num [normalized, padding19, oneGateMargin, fusedSaving,
    shearCharge, baseCount, incidenceCount, value, Nat.choose]

theorem normalized20_eq :
    normalized 20 padding20 = 3249 / 274877906944 := by
  norm_num [normalized, padding20, oneGateMargin, fusedSaving,
    shearCharge, baseCount, incidenceCount, value, Nat.choose]

theorem normalized19_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 19 padding19 := by
  rw [normalized19_eq]
  norm_num

theorem normalized20_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 20 padding20 := by
  rw [normalized20_eq]
  norm_num

end ComplexShearGateCostAuditOneGateH19H20
end ExactFourier
end OAI
