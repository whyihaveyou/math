import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# h = 24 class-weighted all-pair price threshold

`AllPairMomentIdentity` proves the exact three-class scalar identity in the
finite h = 6 model.  This file records the corresponding h = 24 arithmetic
target without pretending that a class price is already implemented by a
frame-labelled gate.  Let `c0`, `c1`, and `c2` be the directional prices for
pairs meeting one fixed target triple in zero, one, and two coordinates.  The
per-target weighted count is

    210*c0 + 63*c1 + 3*c2

The `amortizedMargin` theorem below treats this count as an already-amortized
price against a retained `v^2` invocation block.  A different model may
instead count one fixed-target aggregate family and add an independent factor
`v`; `familyMargin` records that deliberately separate stress test.  It is not
an identity for the physical circuit, and the threshold is only a design
target, not an established saving.
-/

namespace OAI
namespace ExactFourier
namespace AllPairClassArithmeticH24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def m : ℕ := CenterCompression.H24.m
def pairBlock : ℕ := v ^ 2
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def padding : ℕ := CenterCompression.H24.Wstar

def insidePairCount : ℕ := Nat.choose 3 2
def onePairCount : ℕ := 3 * (h - 3)
def zeroPairCount : ℕ := Nat.choose (h - 3) 2

def weightedCount (c0 c1 c2 : ℕ) : ℕ :=
  zeroPairCount * c0 + onePairCount * c1 + insidePairCount * c2

def amortizedMargin (c0 c1 c2 : ℕ) : ℤ :=
  (centreSaving : ℤ) - (pairBlock * weightedCount c0 c1 c2 : ℕ)

def amortizedNormalizedMargin (c0 c1 c2 : ℕ) : ℚ :=
  (amortizedMargin c0 c1 c2 : ℚ) / ((m : ℚ) * (padding : ℚ))

/- An explicit extra target-family replication factor for a stress model. -/
def familyWeightedCount (c0 c1 c2 : ℕ) : ℕ :=
  v * weightedCount c0 c1 c2

def familyMargin (c0 c1 c2 : ℕ) : ℤ :=
  (centreSaving : ℤ) - (pairBlock * familyWeightedCount c0 c1 c2 : ℕ)

theorem h_eq : h = 24 := by
  rfl

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem m_eq : m = 13824 := by
  exact CenterCompression.H24.m_eq

theorem pairBlock_eq : pairBlock = 4096576 := by
  norm_num [pairBlock, v, CenterCompression.H24.v, CenterCompression.H24.h,
    Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem padding_eq : padding = 35184372088832 := by
  exact CenterCompression.H24.Wstar_eq

theorem insidePairCount_eq : insidePairCount = 3 := by
  norm_num [insidePairCount, Nat.choose]

theorem onePairCount_eq : onePairCount = 63 := by
  norm_num [onePairCount, h, CenterCompression.H24.h]

theorem zeroPairCount_eq : zeroPairCount = 210 := by
  norm_num [zeroPairCount, h, CenterCompression.H24.h, Nat.choose]

theorem totalPairCount_eq :
    insidePairCount + onePairCount + zeroPairCount = 276 := by
  norm_num [insidePairCount, onePairCount, zeroPairCount, h,
    CenterCompression.H24.h, Nat.choose]

theorem weightedCount_two_eq : weightedCount 2 2 2 = 552 := by
  norm_num [weightedCount, insidePairCount, onePairCount, zeroPairCount,
    h, CenterCompression.H24.h, Nat.choose]

theorem two_cost_amortized_margin_eq : amortizedMargin 2 2 2 = 163863040 := by
  norm_num [amortizedMargin, weightedCount, centreSaving, pairBlock,
    insidePairCount, onePairCount, zeroPairCount, h, v,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.v,
    CenterCompression.H24.h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, Nat.choose]

theorem two_cost_amortized_normalized_eq :
    amortizedNormalizedMargin 2 2 2 = 320045 / 949978046398464 := by
  norm_num [amortizedNormalizedMargin, amortizedMargin, weightedCount, centreSaving,
    pairBlock, insidePairCount, onePairCount, zeroPairCount, h, v, m,
    padding, CenterCompression.H24.deltaCompressed,
    CenterCompression.H24.v, CenterCompression.H24.h,
    CenterCompression.H24.m, CenterCompression.H24.Wstar,
    CenterCompression.H24.N0, CenterCompression.H24.I0, Nat.choose]

theorem weightedCount_le_of_prices
    (c0 c1 c2 : ℕ) (hq : weightedCount c0 c1 c2 ≤ 473) :
    pairBlock * weightedCount c0 c1 c2 ≤ 1937680448 := by
  have hmul := Nat.mul_le_mul_left pairBlock hq
  norm_num [pairBlock, v, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose] at hmul ⊢
  exact hmul

theorem margin_ge_of_weightedCount_le
    (c0 c1 c2 : ℕ) (hq : weightedCount c0 c1 c2 ≤ 473) :
    (487492544 : ℤ) ≤ amortizedMargin c0 c1 c2 := by
  have hmul := weightedCount_le_of_prices c0 c1 c2 hq
  have hmulZ :
      (pairBlock * weightedCount c0 c1 c2 : ℤ) ≤ 1937680448 := by
    exact_mod_cast hmul
  rw [amortizedMargin, centreSaving_eq]
  omega

theorem amortized_normalized_gt_one_e_minus_nine
    (c0 c1 c2 : ℕ) (hq : weightedCount c0 c1 c2 ≤ 473) :
    (1 : ℚ) / 10 ^ 9 < amortizedNormalizedMargin c0 c1 c2 := by
  have hm := margin_ge_of_weightedCount_le c0 c1 c2 hq
  have hden : (0 : ℚ) < (m : ℚ) * (padding : ℚ) := by
    norm_num [m, padding, CenterCompression.H24.m,
      CenterCompression.H24.h, CenterCompression.H24.Wstar]
  have hmQ : (487492544 : ℚ) ≤ (amortizedMargin c0 c1 c2 : ℚ) := by
    exact_mod_cast hm
  have hbase :
      (1 : ℚ) / 10 ^ 9 < (487492544 : ℚ) /
        ((m : ℚ) * (padding : ℚ)) := by
    norm_num [m, padding, CenterCompression.H24.m,
      CenterCompression.H24.h, CenterCompression.H24.Wstar]
  have hratio :
      (487492544 : ℚ) / ((m : ℚ) * (padding : ℚ)) ≤
        (amortizedMargin c0 c1 c2 : ℚ) / ((m : ℚ) * (padding : ℚ)) := by
    exact div_le_div_of_nonneg_right hmQ (le_of_lt hden)
  exact lt_of_lt_of_le hbase hratio

theorem familyWeightedCount_two_eq : familyWeightedCount 2 2 2 = 1117248 := by
  norm_num [familyWeightedCount, weightedCount, v, insidePairCount,
    onePairCount, zeroPairCount, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem family_two_cost_margin_eq : familyMargin 2 2 2 = -4574466169856 := by
  norm_num [familyMargin, familyWeightedCount, weightedCount, centreSaving,
    pairBlock, v, insidePairCount, onePairCount, zeroPairCount, h,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.v,
    CenterCompression.H24.h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, Nat.choose]

theorem family_c2_one_margin_eq : familyMargin 0 0 1 = -22449236480 := by
  norm_num [familyMargin, familyWeightedCount, weightedCount, centreSaving,
    pairBlock, v, insidePairCount, onePairCount, zeroPairCount, h,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.v,
    CenterCompression.H24.h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, Nat.choose]

end AllPairClassArithmeticH24
end ExactFourier
end OAI
