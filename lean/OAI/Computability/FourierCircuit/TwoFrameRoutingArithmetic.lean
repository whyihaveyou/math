import OAI.Computability.FourierCircuit.ArbitraryTwoFrameCover
import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Exact H24 arithmetic for the dense two-frame routing candidate

`ArbitraryTwoFrameCover` proves the label-level fact that
`u = e₀` and `w = 1 + e₀` cover every weight-three target at even width.
This file records the finite direction ledgers used by the accompanying
Python audit.  The charges are explicit accounting premises: they do not
construct a complex gate, a source-formation schedule, or an all-length DFT
recurrence.  In particular, the normalized values below are route-candidate
width margins, not unconditional exponent gaps.
 -/

namespace OAI
namespace ExactFourier
namespace TwoFrameRoutingArithmetic

open CenterCompression

namespace H24

abbrev h : ℕ := CenterCompression.H24.h
abbrev m : ℕ := CenterCompression.H24.m
abbrev centreSaving : ℤ := CenterCompression.H24.deltaCompressed

def prefixSum : ℕ := 1 + h + h ^ 2
def basePadding : ℕ := 2 ^ 34

/- The two-frame candidate charges two directional units per prefix switch. -/
def switchOnlyCharge : ℕ := 2 * (2 - 1) * prefixSum

/- A block round-trip charges 2(h-1) directions for each of two frames. -/
def blockRoundtripCharge : ℕ := 2 * (h - 1) * 2 * prefixSum

def switchMargin : ℤ := centreSaving - switchOnlyCharge
def blockMargin : ℤ := centreSaving - blockRoundtripCharge

def switchNormalized : ℚ :=
  (switchMargin : ℚ) / ((m : ℚ) * (basePadding : ℚ))

def blockNormalized : ℚ :=
  (blockMargin : ℚ) / ((m : ℚ) * (basePadding : ℚ))

theorem prefixSum_eq : prefixSum = 601 := by
  norm_num [prefixSum, h, CenterCompression.H24.h]

theorem basePadding_eq : basePadding = 17179869184 := by
  norm_num [basePadding]

theorem switchOnlyCharge_eq : switchOnlyCharge = 1202 := by
  norm_num [switchOnlyCharge, prefixSum, h, CenterCompression.H24.h]

theorem blockRoundtripCharge_eq : blockRoundtripCharge = 55292 := by
  norm_num [blockRoundtripCharge, prefixSum, h, CenterCompression.H24.h]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  change (CenterCompression.H24.deltaCompressed : ℤ) = 2425172992
  exact_mod_cast CenterCompression.H24.deltaCompressed_eq

theorem switchMargin_eq : switchMargin = 2425171790 := by
  rw [switchMargin, centreSaving_eq, switchOnlyCharge_eq]
  norm_num

theorem blockMargin_eq : blockMargin = 2425117700 := by
  rw [blockMargin, centreSaving_eq, blockRoundtripCharge_eq]
  norm_num

theorem switchNormalized_eq :
    switchNormalized = 1212585895 / 118747255799808 := by
  rw [switchNormalized, switchMargin_eq, basePadding_eq]
  norm_num [m, CenterCompression.H24.m, h, CenterCompression.H24.h]

theorem blockNormalized_eq :
    blockNormalized = 606279425 / 59373627899904 := by
  rw [blockNormalized, blockMargin_eq, basePadding_eq]
  norm_num [m, CenterCompression.H24.m, h, CenterCompression.H24.h]

theorem switchNormalized_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < switchNormalized := by
  rw [switchNormalized_eq]
  norm_num

theorem blockNormalized_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < blockNormalized := by
  rw [blockNormalized_eq]
  norm_num

end H24
end TwoFrameRoutingArithmetic
end ExactFourier
end OAI
