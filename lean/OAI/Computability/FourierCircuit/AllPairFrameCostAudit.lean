import OAI.Computability.FourierCircuit.CenterCompression
import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# Conditional frame-cost audit for the full pair-aggregate bank

For a fixed pair `F`, the all-target family of off-diagonal pair labels spans the
full pair-label space.  `PairTargetFrameLocal` proves that this space has
finite dimension `h - 2`; at `h = 24` this is `22`.  The cost calculation below
keeps the frame transition explicit.  It compares the optimistic two-unit
charge with a conditional three-unit transition:

* `H -> H_k` charges one unit (a one-dimensional decrease), and
* `H_k -> K_k` charges two units (the codimension-two return to the active
  space).

The arithmetic is exact and conditional.  It does not assert that these
transitions can be scheduled globally, nor that pair aggregates implement the
full side correction.  In particular, the negative corrected margin is useful
precisely because it removes the optimistic saving under this stated charge.
-/

namespace OAI
namespace ExactFourier
namespace AllPairFrameCostAudit
namespace H24

open CenterCompression
open PairTargetFrameLocal

/-- Active binary dimension in the centre-compressed `h = 24` instance. -/
def h : ℕ := CenterCompression.H24.h

/-- Number of source triples through one fixed pair. -/
def v : ℕ := CenterCompression.H24.v

/-- Number of pair labels in one invocation. -/
def pairCount : ℕ := Nat.choose h 2

/-- Number of pair-labelled invocations in one side stage. -/
def pairBlock : ℕ := v ^ 2 * pairCount

/-- Scalar role count for the full pair aggregate proposal. -/
def roleCount : ℕ :=
  2 * CenterCompression.H24.N0 +
    CenterCompression.H24.I0 * (pairCount + h)

/-- Next power-of-two padding for that scalar role count. -/
def padding : ℕ := 2 ^ 35

/-- The previous audit's one-transition, codimension-two charge. -/
def optimisticTransitionCost : ℕ := 2

/-- `H -> H_k` decreases by one dimension.  This is an explicit conditional
assumption about the framed transition, not a theorem about all networks. -/
def downCost : ℕ := 1

/-- `H_k -> K_k` returns across a codimension-two boundary. -/
def upCost : ℕ := 2

/-- The corrected transition charge is the sum of the two directed costs. -/
def correctedTransitionCost : ℕ := downCost + upCost

/-- Optimistic two-unit penalty used by the earlier arithmetic candidate. -/
def optimisticPenalty : ℕ := optimisticTransitionCost * pairBlock

/-- Conditional penalty after charging both `H -> H_k` and `H_k -> K_k`. -/
def correctedPenalty : ℕ := correctedTransitionCost * pairBlock

/-- Centre saving before the pair-boundary charge. -/
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed

/-- The old positive margin, expressed as an integer to make signs explicit. -/
def optimisticMargin : ℤ :=
  (centreSaving : ℤ) - (optimisticPenalty : ℤ)

/-- The corrected margin, expressed in `ℤ` so a failed saving is visible. -/
def correctedMargin : ℤ :=
  (centreSaving : ℤ) - (correctedPenalty : ℤ)

/-- The corrected margin normalized by the multiplier and pair padding. -/
def correctedNormalizedMargin : ℚ :=
  (correctedMargin : ℚ) /
    ((CenterCompression.H24.m : ℚ) * (padding : ℚ))

/-- A fixed pair used to instantiate the local pair-span dimension theorem. -/
def pairF : Finset (Fin 24) := {0, 1}

/-- One target outside the fixed pair. -/
def target : Fin 24 := 2

 theorem h_eq : h = 24 := by
  rfl

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem pairCount_eq : pairCount = 276 := by
  norm_num [pairCount, h, CenterCompression.H24.h, Nat.choose]

theorem pairBlock_eq : pairBlock = 1130654976 := by
  norm_num [pairBlock, v, pairCount, h,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem roleCount_eq : roleCount = 20269858048 := by
  norm_num [roleCount, pairCount, h, v,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem padding_eq : padding = 34359738368 := by
  norm_num [padding]

theorem padding_is_next_power : 2 ^ 34 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, pairCount, h, v, padding,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

/-- The all-target pair span has the expected pair-space dimension. -/
theorem pairF_card : pairF.card = 2 := by
  norm_num [pairF]

theorem pairSpan_finrank_eq :
    Module.finrank (ZMod 2) (pairSpan pairF) = 22 := by
  have hdim := pairSpan_finrank pairF pairF_card
  norm_num at hdim ⊢
  exact hdim

/-- Excluding one target leaves the local source span of dimension `21`. -/
theorem target_not_mem_pairF : target ∉ pairF := by
  norm_num [target, pairF]

theorem sourceSpan_finrank_eq :
    Module.finrank (ZMod 2) (sourceSpan pairF target) = 21 := by
  have hdim := sourceSpan_finrank pairF target pairF_card target_not_mem_pairF
  norm_num at hdim ⊢
  exact hdim

/-- The two pieces of the conditional transition are exactly the advertised
one- and two-unit charges. -/
theorem transition_costs_eq :
    downCost = 1 ∧ upCost = 2 ∧ correctedTransitionCost = 3 := by
  norm_num [downCost, upCost, correctedTransitionCost]

theorem optimisticPenalty_eq : optimisticPenalty = 2261309952 := by
  norm_num [optimisticPenalty, optimisticTransitionCost, pairBlock,
    pairCount, v, h, CenterCompression.H24.v, CenterCompression.H24.h,
    Nat.choose]

theorem correctedPenalty_eq : correctedPenalty = 3391964928 := by
  norm_num [correctedPenalty, correctedTransitionCost, downCost, upCost,
    pairBlock, pairCount, v, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem optimisticMargin_eq : optimisticMargin = 163863040 := by
  norm_num [optimisticMargin, centreSaving, optimisticPenalty,
    optimisticTransitionCost, pairBlock, pairCount, v, h,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

theorem optimisticMargin_pos : 0 < optimisticMargin := by
  rw [optimisticMargin_eq]
  norm_num

/-- Charging the extra unit makes the h=24 margin negative. -/
theorem correctedMargin_eq : correctedMargin = -966791936 := by
  norm_num [correctedMargin, centreSaving, correctedPenalty,
    correctedTransitionCost, downCost, upCost, pairBlock, pairCount,
    v, h, CenterCompression.H24.deltaCompressed,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem correctedMargin_neg : correctedMargin < 0 := by
  rw [correctedMargin_eq]
  norm_num

theorem correctedNormalizedMargin_eq :
    correctedNormalizedMargin = -3776531 / 1855425871872 := by
  norm_num [correctedNormalizedMargin, correctedMargin_eq,
    CenterCompression.H24.m_eq, padding_eq]

theorem correctedNormalizedMargin_neg : correctedNormalizedMargin < 0 := by
  rw [correctedNormalizedMargin_eq]
  norm_num

/-- The corrected charge exceeds the centre saving, so the corresponding
natural-number saving would truncate to zero. -/
theorem correctedPenalty_exceeds_centreSaving : centreSaving < correctedPenalty := by
  norm_num [centreSaving, correctedPenalty, correctedTransitionCost, downCost,
    upCost, pairBlock, pairCount, v, h,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

/-- The optimistic and corrected penalties differ by exactly one full pair
block; this is the arithmetic effect of adding the `H -> H_k` charge. -/
theorem correctedPenalty_minus_optimisticPenalty_eq :
    correctedPenalty - optimisticPenalty = pairBlock := by
  simp [correctedPenalty, optimisticPenalty, correctedTransitionCost,
    optimisticTransitionCost, downCost, upCost]
  omega

end H24
end AllPairFrameCostAudit
end ExactFourier
end OAI
