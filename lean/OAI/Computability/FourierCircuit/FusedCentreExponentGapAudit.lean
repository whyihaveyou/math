import OAI.Computability.FourierCircuit.FusedCentreTransportNaturality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# A rigorous exponent-gap conversion for the six-phase conditional ledger

The finite ledger in `CenterBoundaryShearScheduleAudit` is a normalized saving
`ε`, not the recurrence exponent gap.  If the inherited recurrence multiplier
is `m * (1 - ε)`, the gap is

`-log (1 - ε) / log m`.

This file supplies a concrete h=24 analytic conversion for the six-phase
conditional ledger.  It proves `log 13824 < 11` using a finite exponential
series bound, and then uses `log (1-ε) ≤ -ε`.  The result is still conditional
on the event model and the inherited recurrence formula; it does not prove a
complex gate schedule or an all-length DFT theorem.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreExponentGapAudit

open CenterBoundaryShearScheduleAudit

private lemma exp_one_gt_five_halves :
    (5 : ℝ) / 2 < Real.exp 1 := by
  have h := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hlow := (abs_le.mp h).1
  linarith

private lemma log_h24_lt_eleven :
    Real.log (13824 : ℝ) < 11 := by
  have hexp : (13824 : ℝ) < Real.exp 11 := by
    have hp : (13824 : ℝ) < (5 / 2 : ℝ) ^ 11 := by norm_num
    have hpow : (5 / 2 : ℝ) ^ 11 < (Real.exp 1) ^ 11 := by
      apply pow_lt_pow_left₀ exp_one_gt_five_halves (by positivity)
      norm_num
    rw [show Real.exp 11 = (Real.exp 1) ^ 11 by
      rw [show (11 : ℝ) = (11 : ℕ) * 1 by norm_num, Real.exp_nat_mul]]
    exact hp.trans hpow
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp

def epsilon : ℝ :=
  (CenterBoundaryShearScheduleAudit.H24.sixPhaseNormalized : ℚ)

noncomputable def exponentGap : ℝ :=
  -Real.log (1 - epsilon) / Real.log (13824 : ℝ)

theorem epsilon_eq :
    epsilon = (2624369 : ℝ) / 237494511599616 := by
  rw [epsilon, CenterBoundaryShearScheduleAudit.H24.sixPhaseNormalized_eq]
  norm_num

theorem epsilon_pos : 0 < epsilon := by
  rw [epsilon_eq]
  norm_num

theorem epsilon_lt_one : epsilon < 1 := by
  rw [epsilon_eq]
  norm_num

theorem epsilon_gt_eleven_nano :
    (11 : ℝ) / 10 ^ 9 < epsilon := by
  rw [epsilon_eq]
  norm_num

theorem log_one_sub_epsilon_le_neg_epsilon :
    Real.log (1 - epsilon) ≤ -epsilon := by
  have hpos : 0 < 1 - epsilon := by linarith [epsilon_lt_one]
  have h := Real.log_le_sub_one_of_pos hpos
  convert h using 1 <;> ring

theorem log_h24_pos : 0 < Real.log (13824 : ℝ) :=
  Real.log_pos (by norm_num)

theorem exponentGap_gt_one_e_minus_nine :
    (1 : ℝ) / 10 ^ 9 < exponentGap := by
  rw [exponentGap]
  have hlog := log_h24_lt_eleven
  have hlogpos := log_h24_pos
  have hnum := log_one_sub_epsilon_le_neg_epsilon
  have heps := epsilon_gt_eleven_nano
  apply (lt_div_iff₀ hlogpos).2
  nlinarith

end FusedCentreExponentGapAudit
end ExactFourier
end OAI
