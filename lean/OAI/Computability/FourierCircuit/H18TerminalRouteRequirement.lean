import OAI.Computability.FourierCircuit.H18TerminalInterface
import Mathlib.Tactic

/-!
# Discrete terminal-frame route requirement for the h = 18 candidate

`H18TerminalInterface` proves the common-frame terminal bank costs at least two
residual directions per bank role.  Since frame dimensions are integral, the
bound has a sharper form: the minimum is attained only when the common frame
has one of the two endpoint dimensions (`h` or `h - 1`); every other frame
costs at least six.  The resulting h = 18 deficit bounds are conditional on
the same two-bank/common-frame accounting and are not a lower bound for other
terminal topologies.
-/

namespace OAI
namespace ExactFourier
namespace H18TerminalRouteRequirement

open H18TerminalInterface

/-- A common frame has the minimum terminal cost exactly at either endpoint
of the two incident label dimensions. -/
theorem terminal_cost_eq_two_iff (h ell : ℤ) :
    terminalCost h ell = 2 ↔ ell = h ∨ ell = h - 1 := by
  constructor
  · intro hcost
    by_cases hleft : ell ≤ h - 1
    · have h₁ : 0 ≤ h - ell := by omega
      have h₂ : 0 ≤ (h - 1) - ell := by omega
      unfold terminalCost at hcost
      rw [abs_of_nonneg h₁, abs_of_nonneg h₂] at hcost
      right
      omega
    · have hright : h ≤ ell := by omega
      have h₁ : h - ell ≤ 0 := by omega
      have h₂ : (h - 1) - ell ≤ 0 := by omega
      unfold terminalCost at hcost
      rw [abs_of_nonpos h₁, abs_of_nonpos h₂] at hcost
      left
      omega
  · rintro (rfl | rfl) <;> simp [terminalCost]

/-- If the common frame is not one of the endpoint dimensions, its integral
cost jumps from two directly to at least six. -/
theorem terminal_cost_ge_six_of_nonendpoint
    (h ell : ℤ) (h₁ : ell ≠ h) (h₂ : ell ≠ h - 1) :
    6 ≤ terminalCost h ell := by
  by_cases hleft : ell ≤ h - 1
  · have ha : 0 ≤ h - ell := by omega
    have hb : 0 ≤ (h - 1) - ell := by omega
    unfold terminalCost
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    have hgap : 2 ≤ h - ell := by omega
    omega
  · have hright : h ≤ ell := by omega
    have ha : h - ell ≤ 0 := by omega
    have hb : (h - 1) - ell ≤ 0 := by omega
    unfold terminalCost
    rw [abs_of_nonpos ha, abs_of_nonpos hb]
    have hgap : 1 ≤ ell - h := by omega
    omega

/-- There is no integral intermediate terminal cost: every route is either
at the endpoint price or pays at least six residual directions. -/
theorem terminal_cost_eq_two_or_ge_six (h ell : ℤ) :
    terminalCost h ell = 2 ∨ 6 ≤ terminalCost h ell := by
  by_cases h₁ : ell = h
  · left
    exact (terminal_cost_eq_two_iff h ell).2 (Or.inl h₁)
  by_cases h₂ : ell = h - 1
  · left
    exact (terminal_cost_eq_two_iff h ell).2 (Or.inr h₂)
  right
  exact terminal_cost_ge_six_of_nonendpoint h ell h₁ h₂

/-- Residual accounting when the terminal bank uses a common frame of
integral dimension `ell`.  The coefficient of `N` is the per-role terminal
cost, while the other terms are the one-stage h = 18 ledger. -/
def routeResidual (W N h ell : ℤ) : ℤ :=
  W * h - 2 * N + 2 * (h * h) + terminalCost h ell * N

def routeDeficit (W N h ell : ℤ) : ℤ :=
  W * h - routeResidual W N h ell

/-- At the endpoint common frames, the route residual agrees with the
previous frame-compatible accounting. -/
theorem endpoint_route_residual_eq
    (W N h ell : ℤ) (hell : ell = h ∨ ell = h - 1) :
    routeResidual W N h ell = frameCompatibleResidual W N h := by
  have hcost : terminalCost h ell = 2 :=
    (terminal_cost_eq_two_iff h ell).2 hell
  unfold routeResidual frameCompatibleResidual
  rw [hcost]

/-- Any h = 18 common-frame terminal route has deficit at most -648, even
when it chooses the cheaper endpoint frame. -/
theorem h18_route_deficit_le :
    ∀ ell : ℤ, routeDeficit 409650 816 18 ell ≤ -648 := by
  intro ell
  have hcost := terminal_cost_ge_two 18 ell
  unfold routeDeficit routeResidual
  nlinarith

/-- The endpoint frames attain the exact corrected h = 18 deficit. -/
theorem h18_endpoint_route_deficit_eq
    (ell : ℤ) (hell : ell = 18 ∨ ell = 17) :
    routeDeficit 409650 816 18 ell = -648 := by
  have hcost : terminalCost 18 ell = 2 :=
    (terminal_cost_eq_two_iff 18 ell).2 (by omega)
  unfold routeDeficit routeResidual
  rw [hcost]
  norm_num

/-- If a terminal redesign forces a genuinely different integral common frame,
the h = 18 one-stage deficit is at most -3912. -/
theorem h18_nonendpoint_route_deficit_le
    (ell : ℤ) (h₁ : ell ≠ 18) (h₂ : ell ≠ 17) :
    routeDeficit 409650 816 18 ell ≤ -3912 := by
  have hcost := terminal_cost_ge_six_of_nonendpoint 18 ell h₁ h₂
  unfold routeDeficit routeResidual
  nlinarith

/-- The exploratory one-line terminal charge cannot be realized by this
common-frame route: the per-role cost is never one. -/
theorem h18_common_frame_not_one_line (ell : ℤ) :
    ¬ terminalCost 18 ell ≤ 1 := by
  have hcost := terminal_cost_ge_two 18 ell
  omega

end H18TerminalRouteRequirement
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace H18TerminalRouteRequirement

open H18TerminalInterface

/-! ### Conditional insertion into the h = 18 fused-centre ledger

The h = 18 fused-centre arithmetic certificate has margin `187771392` before
any separately charged terminal bank.  The following definitions do not assert
that a terminal bank has a particular number `q` of roles; they state exactly
how a common-frame charge would alter that already conditional margin if its
baseline ledger had charged one line per role.
-/

/-- Margin after replacing a one-line terminal charge by the common-frame
cost, for an abstract number `q` of terminal roles. -/
def fusedMarginAfterTerminal (q ell : ℤ) : ℤ :=
  187771392 - (terminalCost 18 ell - 1) * q

/-- At either endpoint common frame the h = 18 fused-centre margin loses one
unit for each terminal role. -/
theorem h18_fused_endpoint_margin
    (q ell : ℤ) (hell : ell = 18 ∨ ell = 17) :
    fusedMarginAfterTerminal q ell = 187771392 - q := by
  have hcost : terminalCost 18 ell = 2 :=
    (terminal_cost_eq_two_iff 18 ell).2 (by omega)
  unfold fusedMarginAfterTerminal
  rw [hcost]
  ring

/-- If the terminal common frame is forced away from both endpoint dimensions,
its integral cost loses at least five units per terminal role relative to the
one-line baseline. -/
theorem h18_fused_nonendpoint_margin_le
    (q ell : ℤ) (hq : 0 ≤ q) (h₁ : ell ≠ 18) (h₂ : ell ≠ 17) :
    fusedMarginAfterTerminal q ell ≤ 187771392 - 5 * q := by
  have hcost := terminal_cost_ge_six_of_nonendpoint 18 ell h₁ h₂
  unfold fusedMarginAfterTerminal
  nlinarith

/-- Under the endpoint common-frame route, the conditional h = 18 margin is
positive exactly while the number of terminal roles stays below the margin. -/
theorem h18_fused_endpoint_positive_iff
    (q ell : ℤ) (hell : ell = 18 ∨ ell = 17) (hq : 0 ≤ q) :
    0 < fusedMarginAfterTerminal q ell ↔ q ≤ 187771391 := by
  rw [h18_fused_endpoint_margin q ell hell]
  omega

/-- Under a nonendpoint integral common frame, positivity requires the much
stronger abstract route bound `q ≤ 37554278`. -/
theorem h18_fused_nonendpoint_positive_requires
    (q ell : ℤ) (hq : 0 ≤ q) (h₁ : ell ≠ 18) (h₂ : ell ≠ 17)
    (hpos : 0 < fusedMarginAfterTerminal q ell) :
    q ≤ 37554278 := by
  have hbound := h18_fused_nonendpoint_margin_le q ell hq h₁ h₂
  omega

end H18TerminalRouteRequirement
end ExactFourier
end OAI
