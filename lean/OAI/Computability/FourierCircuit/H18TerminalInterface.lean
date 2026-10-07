import Mathlib.Tactic

/-!
# Terminal bank-gate interface audit for the h = 18 p = 1 candidate

This is a conditional audit of the standard common-frame rule for a two-bank
gate.  It is not a lower bound for circuits that use a different terminal
construction.  It shows that the one-line terminal charge used by the
exploratory h18 arithmetic certificate cannot implement the usual bank gate.
-/

namespace OAI
namespace ExactFourier
namespace H18TerminalInterface

def terminalGap (h ell : ℤ) : ℤ :=
  |h - ell| + |(h - 1) - ell|

theorem terminal_gap_ge_one (h ell : ℤ) :
    1 ≤ terminalGap h ell := by
  unfold terminalGap
  have htri := abs_sub_le h ell (h - 1)
  have hunit : |h - (h - 1)| = (1 : ℤ) := by norm_num
  have hrev : |ell - (h - 1)| = |(h - 1) - ell| := abs_sub_comm _ _
  rw [hunit, hrev] at htri
  exact htri

def terminalCost (h ell : ℤ) : ℤ :=
  2 * |h - ell| + 2 * |(h - 1) - ell|

theorem terminal_cost_ge_two (h ell : ℤ) :
    2 ≤ terminalCost h ell := by
  dsimp [terminalCost]
  have hgap := terminal_gap_ge_one h ell
  simp only [terminalGap] at hgap
  linarith

def candidateResidual (W N h : ℤ) : ℤ :=
  W * h - 2 * N + 2 * (h * h) + N

def frameCompatibleResidual (W N h : ℤ) : ℤ :=
  W * h - 2 * N + 2 * (h * h) + 2 * N

def candidateDeficit (W N h : ℤ) : ℤ :=
  W * h - candidateResidual W N h

def frameCompatibleDeficit (W N h : ℤ) : ℤ :=
  W * h - frameCompatibleResidual W N h

def frameCompatibleLambda : ℚ :=
  18 + (648 : ℚ) / (2 ^ 19 : ℚ)

theorem frame_compatible_residual_eq_candidate_plus (W N h : ℤ) :
    frameCompatibleResidual W N h = candidateResidual W N h + N := by
  dsimp [frameCompatibleResidual, candidateResidual]
  ring

theorem candidate_residual_equiv (W N h : ℤ) :
    candidateResidual W N h = W * h - N + 2 * (h * h) := by
  dsimp [candidateResidual]
  ring

theorem candidate_deficit_formula (W N h : ℤ) :
    candidateDeficit W N h = N - 2 * (h * h) := by
  dsimp [candidateDeficit, candidateResidual]
  ring

theorem frame_compatible_deficit_formula (W N h : ℤ) :
    frameCompatibleDeficit W N h = -2 * (h * h) := by
  dsimp [frameCompatibleDeficit, frameCompatibleResidual]
  ring

theorem h18_candidate_deficit :
    candidateDeficit 409650 816 18 = 168 := by
  norm_num [candidateDeficit, candidateResidual]

theorem h18_frame_compatible_deficit :
    frameCompatibleDeficit 409650 816 18 = -648 := by
  norm_num [frameCompatibleDeficit, frameCompatibleResidual]

theorem h18_missing_terminal_charge :
    frameCompatibleResidual 409650 816 18 - candidateResidual 409650 816 18 =
      816 := by
  norm_num [frameCompatibleResidual, candidateResidual]

theorem h18_frame_compatible_lambda :
    frameCompatibleLambda = 1179729 / 65536 := by
  norm_num [frameCompatibleLambda]

theorem h18_frame_compatible_lambda_gt_m :
    (18 : ℚ) < frameCompatibleLambda := by
  norm_num [frameCompatibleLambda]

theorem h18_terminal_cost_not_one (ell : ℤ) :
    ¬ terminalCost 18 ell = 1 := by
  intro hcost
  have hbound := terminal_cost_ge_two 18 ell
  linarith

end H18TerminalInterface
end ExactFourier
end OAI
