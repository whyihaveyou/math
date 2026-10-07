import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Mixed-radix padding audit for the h = 24 centre-compressed candidate

The fixed-network recursion in the explicit Fourier proof is organized into
binary address columns.  A recursive directional step has exactly
`2^(k-f)` independent fibres.  An invocation on a batch of `B` role arrays
therefore has to use a width `B` dividing that power of two; in particular a
uniform batch width is itself a power of two.  This file records the exact
arithmetic consequence for the h = 24 candidate: every admissible batch that
contains all `W` roles has width at least `2^45`, so replacing the one padded
batch by a mixed collection of admissible batches cannot improve the role
padding term.  The statement is deliberately limited to this binary-column
recursion; it is not a lower bound for a redesigned network or for the outer
mixed-radix length decomposition.
-/

namespace OAI
namespace ExactFourier
namespace MixedRadixPaddingAudit

open CenterCompression

namespace H24

/-- The role width and the (power-of-two) padded width used in the centre
compressed h=24 arithmetic. -/
def roleWidth : ℕ := CenterCompression.H24.Wcompressed
def paddedWidth : ℕ := CenterCompression.H24.Wstar
def directionalSaving : ℕ := CenterCompression.H24.deltaCompressed
def columnCount : ℕ := CenterCompression.H24.m

theorem roleWidth_eq : roleWidth = 34666930287616 := by
  exact CenterCompression.H24.Wcompressed_eq

theorem paddedWidth_eq : paddedWidth = 35184372088832 := by
  exact CenterCompression.H24.Wstar_eq

theorem directionalSaving_eq : directionalSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem columnCount_eq : columnCount = 13824 := by
  exact CenterCompression.H24.m_eq

theorem roleWidth_gt_pow44 : 2 ^ 44 < roleWidth := by
  exact (CenterCompression.H24.Wstar_bounds).1

/-- Any binary batch large enough to carry the full role bank is at least the
next power of two.  The proof uses only the exact h=24 width inequality. -/
theorem powerBatch_lower_bound (b : ℕ)
    (hfit : roleWidth ≤ 2 ^ b) :
    paddedWidth ≤ 2 ^ b := by
  by_contra hnot
  have hlt : 2 ^ b < paddedWidth := lt_of_not_ge hnot
  rw [paddedWidth_eq] at hlt
  have hb : b < 45 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  have hb' : b ≤ 44 := by omega
  have hpow : 2 ^ b ≤ 2 ^ 44 := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hb'
  rw [roleWidth_eq] at hfit
  norm_num at hfit hpow
  omega

/-- Normalized directional saving for a batch width `B`. -/
def normalizedSaving (B : ℕ) : ℚ :=
  (directionalSaving : ℚ) / ((columnCount : ℚ) * (B : ℚ))

theorem normalizedSaving_at_padding :
    normalizedSaving paddedWidth = 2368333 / 474989023199232 := by
  norm_num [normalizedSaving, directionalSaving, columnCount, paddedWidth,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.m,
    CenterCompression.H24.Wstar, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

/-- Enlarging a binary batch can only decrease its normalized saving. -/
theorem normalizedSaving_power_le_padding (b : ℕ)
    (hfit : roleWidth ≤ 2 ^ b) :
    normalizedSaving (2 ^ b) ≤ normalizedSaving paddedWidth := by
  have hpad : paddedWidth ≤ 2 ^ b := powerBatch_lower_bound b hfit
  have hpadQ : (paddedWidth : ℚ) ≤ ((2 ^ b : ℕ) : ℚ) := by
    exact_mod_cast hpad
  have hm : 0 < (columnCount : ℚ) := by
    norm_num [columnCount, CenterCompression.H24.m, CenterCompression.H24.h]
  have hs : 0 ≤ (directionalSaving : ℚ) := by
    norm_num [directionalSaving, CenterCompression.H24.deltaCompressed,
      CenterCompression.H24.N0, CenterCompression.H24.I0,
      CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]
  have hB : 0 < ((2 ^ b : ℕ) : ℚ) := by positivity
  have hp : 0 < (paddedWidth : ℚ) := by
    norm_num [paddedWidth, CenterCompression.H24.Wstar]
  unfold normalizedSaving
  apply (div_le_div_iff₀ (mul_pos hm hB) (mul_pos hm hp)).2
  gcongr

theorem normalizedSaving_power_le_exact_value (b : ℕ)
    (hfit : roleWidth ≤ 2 ^ b) :
    normalizedSaving (2 ^ b) ≤ 2368333 / 474989023199232 := by
  calc
    normalizedSaving (2 ^ b) ≤ normalizedSaving paddedWidth :=
      normalizedSaving_power_le_padding b hfit
    _ = 2368333 / 474989023199232 := normalizedSaving_at_padding

/-- The unpadded arithmetic denominator is only modestly better; this is the
absolute best one could get by deleting the padding without changing any
role count or recursive interface. -/
theorem normalizedSaving_unpadded :
    (directionalSaving : ℚ) /
        ((columnCount : ℚ) * (roleWidth : ℚ)) = 37 / 7311527424 := by
  norm_num [directionalSaving, columnCount, roleWidth,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.m,
    CenterCompression.H24.Wcompressed, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.dNbr, CenterCompression.H24.h, Nat.choose]

/-- For the current recursion, mixed binary batches have no better per-role
saving than the least admissible batch.  A schedule can use larger powers of
two, but each such invocation is bounded by this same rational value. -/
theorem mixed_binary_batch_no_improvement (b : ℕ)
    (hfit : roleWidth ≤ 2 ^ b) :
    normalizedSaving (2 ^ b) ≤ 2368333 / 474989023199232 :=
  normalizedSaving_power_le_exact_value b hfit

end H24
end MixedRadixPaddingAudit
end ExactFourier
end OAI
