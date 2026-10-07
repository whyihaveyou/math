import OAI.Computability.FourierCircuit.FusedCentreBoundaryArithmeticH16H17H18
import OAI.Computability.FourierCircuit.H18TerminalInterface

/-!
# Joint audit for the h = 16, 17, 18 fused-centre candidates

This file only packages already-proved arithmetic and interface facts.  The
three fused-centre margins exceed `10⁻⁹` under their stated role-count and
power-of-two padding formulas.  At `h = 18`, however, the standard
common-frame terminal interface cannot have the exploratory one-line charge:
its terminal cost is always at least two.  Thus the first conjunct below is a
conditional arithmetic certificate, while the second records an obstruction
to reading that certificate as a physical circuit or an all-length theorem.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreBoundaryAudit

open FusedCentreBoundaryArithmeticH16H17H18
open H18TerminalInterface

/-! All three published one-boundary ledgers clear the `10⁻⁹` arithmetic
target, with the exact power-of-two paddings used by their role counts. -/
theorem h16_h17_h18_margins_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 16 padding16 ∧
      (1 : ℚ) / 10 ^ 9 < normalized 17 padding17 ∧
      (1 : ℚ) / 10 ^ 9 < normalized 18 padding18 := by
  exact ⟨normalized16_gt_one_e_minus_nine,
    normalized17_gt_one_e_minus_nine,
    normalized18_gt_one_e_minus_nine⟩

/-! The h = 18 arithmetic margin and the standard terminal interface audit
must be reported together.  No terminal location can realize a one-unit
common-frame charge. -/
theorem h18_margin_and_terminal_obstruction (ell : ℤ) :
    (1 : ℚ) / 10 ^ 9 < normalized 18 padding18 ∧
      ¬ terminalCost 18 ell = 1 := by
  exact ⟨normalized18_gt_one_e_minus_nine,
    h18_terminal_cost_not_one ell⟩

end FusedCentreBoundaryAudit
end ExactFourier
end OAI
