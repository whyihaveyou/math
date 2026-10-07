import OAI.Computability.FourierCircuit.FusedCentreBoundaryArithmeticH16H17H18
import OAI.Computability.FourierCircuit.H18TerminalRouteRequirement
import Mathlib.Tactic

/-!
# Conditional terminal-route accounting for h = 16, 17, 18

The fused-centre ledger in `FusedCentreBoundaryArithmeticH16H17H18` leaves a
margin before a separately charged terminal bank.  The standard common-frame
interface charges `terminalCost h ell` residual directions per terminal role;
the exploratory ledger had already charged one direction per role.  This
file instantiates the resulting *route-specific* correction under the
explicit assumption that the terminal bank has one role per incidence.

The endpoint common frames (`ell = h` or `ell = h - 1`) therefore cost one
extra unit per incidence role.  All three arithmetic margins remain positive
and above `10⁻⁹` after that correction.  This is an unimplemented compression
target: if the terminal gate instead requires one role per `baseCount h = v³`
bank entry, all three endpoint margins are negative.  The statements are
only arithmetic certificates for these explicit role-count models: they do
not construct a terminal gate, prove scalar/gate commutation, or give a
circuit/all-length DFT theorem.  The generic route audit still proves that a
nonendpoint integral frame costs at least five extra units per role.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreTerminalRouteAudit

open FusedCentreBoundaryArithmeticH16H17H18
open H18TerminalInterface
open H18TerminalRouteRequirement

/- The route correction relative to the one-line baseline. -/
def adjustedMargin (h : ℕ) (ell : ℤ) : ℤ :=
  fusedMargin h - (terminalCost (h : ℤ) ell - 1) * (incidenceCount h : ℤ)

/- One terminal role per incidence is the explicit route-specific premise
   encoded by the multiplier `incidenceCount h`; no universal role-count
   claim is made here. -/
def endpointMargin (h : ℕ) : ℤ := adjustedMargin h (h : ℤ)

def endpointNormalized (h padding : ℕ) : ℚ :=
  (endpointMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

/- The alternative, uncompressed terminal route has one role for each entry
   of a bank indexed by three triple coordinates. -/
def fullBankMargin (h : ℕ) (ell : ℤ) : ℤ :=
  fusedMargin h - (terminalCost (h : ℤ) ell - 1) * (baseCount h : ℤ)

theorem endpointMargin16_eq : endpointMargin 16 = 14112000 := by
  norm_num [endpointMargin, adjustedMargin, fusedMargin, fusedSaving,
    shearCharge, incidenceCount, baseCount, value, neighborDegree,
    terminalCost, Nat.choose]

theorem endpointMargin17_eq : endpointMargin 17 = 69360000 := by
  norm_num [endpointMargin, adjustedMargin, fusedMargin, fusedSaving,
    shearCharge, incidenceCount, baseCount, value, neighborDegree,
    terminalCost, Nat.choose]

theorem endpointMargin18_eq : endpointMargin 18 = 185773824 := by
  norm_num [endpointMargin, adjustedMargin, fusedMargin, fusedSaving,
    shearCharge, incidenceCount, baseCount, value, neighborDegree,
    terminalCost, Nat.choose]

theorem endpointMargin_eq_fusedMargin_sub_incidence (h : ℕ) :
    endpointMargin h = fusedMargin h - (incidenceCount h : ℤ) := by
  unfold endpointMargin adjustedMargin
  have hcost : terminalCost (h : ℤ) (h : ℤ) = 2 := by
    simp [terminalCost]
  rw [hcost]
  ring

theorem endpointRoute16_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < endpointNormalized 16 padding16 := by
  rw [endpointNormalized, endpointMargin16_eq]
  norm_num [padding16]

theorem endpointRoute17_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < endpointNormalized 17 padding17 := by
  rw [endpointNormalized, endpointMargin17_eq]
  norm_num [padding17]

theorem endpointRoute18_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < endpointNormalized 18 padding18 := by
  rw [endpointNormalized, endpointMargin18_eq]
  norm_num [padding18]

theorem endpoint_routes_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < endpointNormalized 16 padding16 ∧
      (1 : ℚ) / 10 ^ 9 < endpointNormalized 17 padding17 ∧
      (1 : ℚ) / 10 ^ 9 < endpointNormalized 18 padding18 := by
  exact ⟨endpointRoute16_gt_one_e_minus_nine,
    endpointRoute17_gt_one_e_minus_nine,
    endpointRoute18_gt_one_e_minus_nine⟩

/- At any common frame, the route-specific margin cannot exceed the endpoint
   value: the generic terminal interface has cost at least two. -/
theorem adjustedMargin_le_endpointMargin
    (h : ℕ) (ell : ℤ) (hinc : 0 ≤ (incidenceCount h : ℤ)) :
    adjustedMargin h ell ≤ endpointMargin h := by
  have hcost : 2 ≤ terminalCost (h : ℤ) ell :=
    terminal_cost_ge_two (h : ℤ) ell
  have hend : terminalCost (h : ℤ) (h : ℤ) = 2 := by
    simp [terminalCost]
  change fusedMargin h - (terminalCost (h : ℤ) ell - 1) *
      (incidenceCount h : ℤ) ≤
    fusedMargin h - (terminalCost (h : ℤ) (h : ℤ) - 1) *
      (incidenceCount h : ℤ)
  rw [hend]
  nlinarith

/- If the common frame is not either endpoint, the six-direction jump costs
   at least five extra units over the one-line baseline per incidence role. -/
theorem adjustedMargin_le_nonendpoint
    (h : ℕ) (ell : ℤ) (hinc : 0 ≤ (incidenceCount h : ℤ))
    (hle : ell ≠ (h : ℤ)) (hle' : ell ≠ (h : ℤ) - 1) :
    adjustedMargin h ell ≤
      fusedMargin h - 5 * (incidenceCount h : ℤ) := by
  have hcost := terminal_cost_ge_six_of_nonendpoint (h : ℤ) ell hle hle'
  unfold adjustedMargin
  nlinarith

theorem nonendpointMargin16_le :
    ∀ ell : ℤ, ell ≠ 16 → ell ≠ 15 → adjustedMargin 16 ell ≤ 10348800 := by
  intro ell h₁ h₂
  have hbound := adjustedMargin_le_nonendpoint 16 ell (by norm_num) h₁ h₂
  norm_num [fusedMargin, fusedSaving, shearCharge, incidenceCount,
    baseCount, value, neighborDegree, Nat.choose] at hbound ⊢
  exact hbound

theorem nonendpointMargin17_le :
    ∀ ell : ℤ, ell ≠ 17 → ell ≠ 16 → adjustedMargin 17 ell ≤ 63811200 := by
  intro ell h₁ h₂
  have hbound := adjustedMargin_le_nonendpoint 17 ell (by norm_num) h₁ h₂
  norm_num [fusedMargin, fusedSaving, shearCharge, incidenceCount,
    baseCount, value, neighborDegree, Nat.choose] at hbound ⊢
  exact hbound

theorem nonendpointMargin18_le :
    ∀ ell : ℤ, ell ≠ 18 → ell ≠ 17 → adjustedMargin 18 ell ≤ 177783552 := by
  intro ell h₁ h₂
  have hbound := adjustedMargin_le_nonendpoint 18 ell (by norm_num) h₁ h₂
  norm_num [fusedMargin, fusedSaving, shearCharge, incidenceCount,
    baseCount, value, neighborDegree, Nat.choose] at hbound ⊢
  exact hbound

theorem fullBankEndpointMargin16_eq : fullBankMargin 16 16 = -160563200 := by
  norm_num [fullBankMargin, fusedMargin, fusedSaving, shearCharge,
    incidenceCount, baseCount, value, terminalCost, Nat.choose]

theorem fullBankEndpointMargin17_eq : fullBankMargin 17 17 = -243684800 := by
  norm_num [fullBankMargin, fusedMargin, fusedSaving, shearCharge,
    incidenceCount, baseCount, value, terminalCost, Nat.choose]

theorem fullBankEndpointMargin18_eq : fullBankMargin 18 18 = -355567104 := by
  norm_num [fullBankMargin, fusedMargin, fusedSaving, shearCharge,
    incidenceCount, baseCount, value, terminalCost, Nat.choose]

theorem fullBankMargin_le_endpointMargin (h : ℕ) (ell : ℤ) :
    fullBankMargin h ell ≤ fullBankMargin h (h : ℤ) := by
  have hcost := terminal_cost_ge_two (h : ℤ) ell
  have hend : terminalCost (h : ℤ) (h : ℤ) = 2 := by
    simp [terminalCost]
  have hbase : 0 ≤ (baseCount h : ℤ) := by positivity
  unfold fullBankMargin
  rw [hend]
  nlinarith

/- A full bank route cannot repair its negative endpoint ledger by choosing
   a different integral common frame.  This remains route-specific. -/
theorem fullBank_routes_negative (ell16 ell17 ell18 : ℤ) :
    fullBankMargin 16 ell16 < 0 ∧
      fullBankMargin 17 ell17 < 0 ∧
      fullBankMargin 18 ell18 < 0 := by
  have h16 := fullBankMargin_le_endpointMargin 16 ell16
  have h17 := fullBankMargin_le_endpointMargin 17 ell17
  have h18 := fullBankMargin_le_endpointMargin 18 ell18
  norm_num only [Nat.cast_ofNat] at h16 h17 h18
  rw [fullBankEndpointMargin16_eq] at h16
  rw [fullBankEndpointMargin17_eq] at h17
  rw [fullBankEndpointMargin18_eq] at h18
  omega

end FusedCentreTerminalRouteAudit
end ExactFourier
end OAI
