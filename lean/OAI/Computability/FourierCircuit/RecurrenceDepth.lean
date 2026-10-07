import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI
namespace Recurrence

/-!
A finite-depth estimate for divide-and-conquer recurrences.  The theorem is
agnostic about what `T` measures; the additive term `A` may represent all
non-recursive work in one call.  The supplied depth function `d` is kept
abstract so that a separate lemma can instantiate it with a logarithmic depth.
-/

theorem bound_of_depth
    (T : ℕ → ℝ) (m K : ℕ) (lambda A D C : ℝ) (d : ℕ → ℕ)
    (hm : 1 < m) (hK : 0 < K) (hlambda : 1 ≤ lambda)
    (hC : 0 ≤ C)
    (habsorb : A + D ≤ lambda * D)
    (hbase : ∀ k, k < K → T k + D ≤ C)
    (hrec : ∀ k, K ≤ k → T k ≤ A + lambda * T (k / m))
    (hdepth : ∀ k, K ≤ k → d (k / m) + 1 ≤ d k) :
    ∀ k, T k + D ≤ C * lambda ^ d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < K
      · have hpow : 1 ≤ lambda ^ d k := one_le_pow₀ hlambda
        have hCpow : C ≤ C * lambda ^ d k :=
          le_mul_of_one_le_right hC hpow
        linarith [hbase k hk]
      · have hKk : K ≤ k := Nat.le_of_not_gt hk
        have hkpos : 0 < k := Nat.zero_lt_of_lt (lt_of_lt_of_le hK hKk)
        have hdiv : k / m < k := Nat.div_lt_self hkpos hm
        have hsub := ih (k / m) hdiv
        have hmul := mul_le_mul_of_nonneg_left hsub (zero_le_one.trans hlambda)
        have hrec' := hrec k hKk
        have hstep : T k + D ≤
            A + lambda * (C * lambda ^ d (k / m) - D) + D := by
          linarith
        calc
          T k + D ≤ A + lambda * (C * lambda ^ d (k / m) - D) + D := hstep
          _ = C * (lambda ^ d (k / m) * lambda) + (A + D - lambda * D) := by
            ring
          _ ≤ C * (lambda ^ d (k / m) * lambda) := by
            linarith
          _ = C * lambda ^ (d (k / m) + 1) := by rw [pow_succ]
          _ ≤ C * lambda ^ d k := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hlambda (hdepth k hKk)) hC

end Recurrence
end OAI
