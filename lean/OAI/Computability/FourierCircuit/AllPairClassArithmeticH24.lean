import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# h = 24 class-weighted all-pair price threshold

`AllPairMomentIdentity` proves the exact three-class scalar identity in the
finite h = 6 model.  This file records the corresponding h = 24 arithmetic
target without pretending that a class price is already implemented by a
frame-labelled gate.  Let `c0`, `c1`, and `c2` be the directional prices for
pairs meeting the fixed target triple in zero, one, and two coordinates.  The
target-independent all-pair bank then pays the weighted count

    210*c0 + 63*c1 + 3*c2

per invocation block.  The theorem below shows exactly how small that count
must be to retain a normalized margin above `10^-9`.
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

def margin (c0 c1 c2 : ℕ) : ℤ :=
  (centreSaving : ℤ) - (pairBlock * weightedCount c0 c1 c2 : ℕ)

def normalizedMargin (c0 c1 c2 : ℕ) : ℚ :=
  (margin c0 c1 c2 : ℚ) / ((m : ℚ) * (padding : ℚ))

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

theorem two_cost_margin_eq : margin 2 2 2 = 163863040 := by
  norm_num [margin, weightedCount, centreSaving, pairBlock,
    insidePairCount, onePairCount, zeroPairCount, h, v,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.v,
    CenterCompression.H24.h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, Nat.choose]

theorem two_cost_normalized_eq :
    normalizedMargin 2 2 2 = 320045 / 949978046398464 := by
  norm_num [normalizedMargin, margin, weightedCount, centreSaving,
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
    (487492544 : ℤ) ≤ margin c0 c1 c2 := by
  have hmul := weightedCount_le_of_prices c0 c1 c2 hq
  have hmulZ :
      (pairBlock * weightedCount c0 c1 c2 : ℤ) ≤ 1937680448 := by
    exact_mod_cast hmul
  rw [margin, centreSaving_eq]
  omega

theorem normalized_gt_one_e_minus_nine
    (c0 c1 c2 : ℕ) (hq : weightedCount c0 c1 c2 ≤ 473) :
    (1 : ℚ) / 10 ^ 9 < normalizedMargin c0 c1 c2 := by
  have hm := margin_ge_of_weightedCount_le c0 c1 c2 hq
  have hden : (0 : ℚ) < (m : ℚ) * (padding : ℚ) := by
    norm_num [m, padding, CenterCompression.H24.m,
      CenterCompression.H24.h, CenterCompression.H24.Wstar]
  have hmQ : (487492544 : ℚ) ≤ (margin c0 c1 c2 : ℚ) := by
    exact_mod_cast hm
  have hbase :
      (1 : ℚ) / 10 ^ 9 < (487492544 : ℚ) /
        ((m : ℚ) * (padding : ℚ)) := by
    norm_num [m, padding, CenterCompression.H24.m,
      CenterCompression.H24.h, CenterCompression.H24.Wstar]
  have hratio :
      (487492544 : ℚ) / ((m : ℚ) * (padding : ℚ)) ≤
        (margin c0 c1 c2 : ℚ) / ((m : ℚ) * (padding : ℚ)) := by
    exact div_le_div_of_nonneg_right hmQ (le_of_lt hden)
  exact lt_of_lt_of_le hbase hratio

end AllPairClassArithmeticH24
end ExactFourier
end OAI
