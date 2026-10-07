import OAI.Computability.FourierCircuit.PairComplementSideArithmetic
import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import Mathlib.Tactic

/-!
# Aggregate-wise boundary ledger for the pair/complement candidate

The common row-5 frame charges every target-dependent pair aggregate through
the full active factor.  A possible escape is to give each aggregate its own
non-common boundary: if its support span has rank `r = h - 2`, the four
successive residual dimensions are

```
  (e - 1) r,   (e - 1) (h - r) + r,   h - r,   0,
```

where `e` is the prefix size.  This file formalizes the resulting ledger.
Under exactly that rank and boundary premise its total is `e*h`, so the
aggregate-wise route preserves the old per-role side charge while using the
smaller pair/complement scalar bank.  The file intentionally does not assert
that a complex gate schedule realizes the premise; the support rank of the
`A` bank is certified, while the corresponding `B`-bank transport and the
aggregate-wise gate composition remain open obligations.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementAggregateBoundary

open PairTargetFrameLocal

/-! A block with active prefix size `e` and support rank `r`. -/

def edgeZero (e r : ℕ) : ℕ := (e - 1) * r

def edgeZeroToTwo (e h r : ℕ) : ℕ := (e - 1) * (h - r) + r

def edgeTwoToFive (h r : ℕ) : ℕ := h - r

def edgeFiveToSeven : ℕ := 0

def blockCost (e h r : ℕ) : ℕ :=
  edgeZero e r + edgeZeroToTwo e h r + edgeTwoToFive h r + edgeFiveToSeven

theorem blockCost_eq_e_mul_h {e h r : ℕ} (he : 1 ≤ e) (hh : 2 ≤ h)
    (hr : r = h - 2) :
    blockCost e h r = e * h := by
  have hcodim : h - (h - 2) = 2 := by omega
  rw [blockCost, edgeZero, edgeZeroToTwo, edgeTwoToFive,
    edgeFiveToSeven, hr, hcodim]
  let a : ℕ := e - 1
  let b : ℕ := h - 2
  have heq : e = a + 1 := by
    dsimp [a]
    omega
  have hEq : h = b + 2 := by
    dsimp [b]
    omega
  change a * b + (a * 2 + b) + 2 = e * h
  rw [heq, hEq]
  ring

/-! The four displayed edge charges separately expose the non-common frame. -/

theorem edgeZero_eq {e h : ℕ} (hr : 2 ≤ h) :
    edgeZero e (h - 2) = (e - 1) * (h - 2) := by
  rfl

theorem edgeZeroToTwo_eq {e h : ℕ} (hr : 2 ≤ h) :
    edgeZeroToTwo e h (h - 2) = 2 * (e - 1) + (h - 2) := by
  rw [edgeZeroToTwo]
  have hc : h - (h - 2) = 2 := by omega
  rw [hc]
  ring

theorem edgeTwoToFive_eq {h : ℕ} (hh : 2 ≤ h) :
    edgeTwoToFive h (h - 2) = 2 := by
  rw [edgeTwoToFive]
  omega

theorem edgeFiveToSeven_eq : edgeFiveToSeven = 0 := rfl

def aggregateStageCost (e h : ℕ) : ℕ := blockCost e h (h - 2)

theorem aggregateStageCost_eq {e h : ℕ} (he : 1 ≤ e) (hh : 2 ≤ h) :
    aggregateStageCost e h = e * h := by
  exact blockCost_eq_e_mul_h he hh rfl

theorem aggregateStageCost_edges {e h : ℕ} (he : 1 ≤ e) (hh : 2 ≤ h) :
    aggregateStageCost e h =
      ((e - 1) * (h - 2)) + (2 * (e - 1) + (h - 2)) + 2 := by
  have h0 := edgeZero_eq (e := e) (h := h) hh
  have h02 := edgeZeroToTwo_eq (e := e) (h := h) hh
  have h25 := edgeTwoToFive_eq (h := h) hh
  unfold aggregateStageCost blockCost
  rw [h0, h02, h25, edgeFiveToSeven_eq]

/-! The paper's three finite prefix sizes are `1`, `h`, and `h²`. -/

def threeStageBoundaryCost (h : ℕ) : ℕ :=
  aggregateStageCost 1 h + aggregateStageCost h h +
    aggregateStageCost (h * h) h

theorem threeStageBoundaryCost_eq {h : ℕ} (hh : 2 ≤ h) :
    threeStageBoundaryCost h = h * (1 + h + h * h) := by
  have hsquare : 1 ≤ h * h := by nlinarith
  rw [threeStageBoundaryCost,
    aggregateStageCost_eq (e := 1) (h := h) (by omega) hh,
    aggregateStageCost_eq (e := h) (h := h) (by omega) hh,
    aggregateStageCost_eq (e := h * h) (h := h) hsquare hh]
  ring

namespace H24

def h : ℕ := 24
def threeStageCost : ℕ := PairComplementAggregateBoundary.threeStageBoundaryCost h

theorem h_eq : h = 24 := rfl

theorem threeStageCost_eq : threeStageCost = 14424 := by
  norm_num [threeStageCost, threeStageBoundaryCost, aggregateStageCost,
    blockCost, edgeZero, edgeZeroToTwo, edgeTwoToFive, edgeFiveToSeven, h]

theorem threeStageCost_formula :
    threeStageCost = h * (1 + h + h * h) := by
  exact threeStageBoundaryCost_eq (by norm_num [h])

/- The pair-span half of the rank premise is an actual Lean fact. -/
theorem pair_span_rank (F : Finset (Fin 24)) (hF : F.card = 2) :
    Module.finrank (ZMod 2) (pairSpan F) = 22 := by
  simpa using (pairSpan_finrank F hF)

/- The second pair bank has to supply the analogous rank/transport lemma. -/
def aggregateBoundaryPremise : Prop :=
  ∀ e : ℕ, 1 ≤ e →
    ∀ r : ℕ, r = h - 2 → blockCost e h r = e * h

theorem aggregateBoundaryPremise_holds : aggregateBoundaryPremise := by
  intro e he r hr
  exact blockCost_eq_e_mul_h he (by norm_num [h]) hr

/- The scalar candidate's normalized gap remains positive under this ledger. -/
theorem candidate_normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 <
      PairComplementSideArithmetic.H24.normalized := by
  exact PairComplementSideArithmetic.H24.normalized_gt_one_e_minus_nine

end H24
end PairComplementAggregateBoundary
end ExactFourier
end OAI
