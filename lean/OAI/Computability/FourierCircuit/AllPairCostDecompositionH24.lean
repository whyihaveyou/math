import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Separating the h = 24 all-pair cost factors

The three class sizes `(210, 63, 3)` are counts for one fixed target triple.
They should not be silently multiplied by an invocation block whose meaning
already includes target addresses.  This file keeps the factors separate:

* `fixedTargetWeight` is the class price for one target;
* `targetReadoutCost` adds the `v = 2024` target readouts;
* `frameSlotCost` uses an independent frame-slot block `B`.

The resulting `separatedLedgerCost` is only an arithmetic ledger.  It does
not assert a physical gate schedule or decide whether a proposed `B` already
contains target replication.
-/

namespace OAI
namespace ExactFourier
namespace AllPairCostDecompositionH24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def pairCount : ℕ := Nat.choose h 2

/-- Pair classes seen from one fixed target triple. -/
def fixedTargetZero : ℕ := Nat.choose (h - 3) 2
def fixedTargetOne : ℕ := 3 * (h - 3)
def fixedTargetTwo : ℕ := Nat.choose 3 2

def fixedTargetWeight (c0 c1 c2 : ℕ) : ℕ :=
  fixedTargetZero * c0 + fixedTargetOne * c1 + fixedTargetTwo * c2

/-- The same class count after summing the target-indexed readouts. -/
def targetReadoutCost (c0 c1 c2 : ℕ) : ℕ :=
  v * fixedTargetWeight c0 c1 c2

/-- A frame-slot block is kept independent of the target-readout factor. -/
def frameSlotCost (B c0 c1 c2 : ℕ) : ℕ :=
  B * fixedTargetWeight c0 c1 c2

def separatedLedgerCost (B c0 c1 c2 : ℕ) : ℕ :=
  frameSlotCost B c0 c1 c2 + targetReadoutCost c0 c1 c2

/-- Fixed-pair counts for the same target/pair incidence relation. -/
def fixedPairZero : ℕ := Nat.choose 22 3
def fixedPairOne : ℕ := 2 * Nat.choose 22 2
def fixedPairTwo : ℕ := 22

def fixedPairWeight (c0 c1 c2 : ℕ) : ℕ :=
  fixedPairZero * c0 + fixedPairOne * c1 + fixedPairTwo * c2

theorem h_eq : h = 24 := by
  rfl

theorem v_eq : v = 2024 := by
  exact CenterCompression.H24.v_eq

theorem pairCount_eq : pairCount = 276 := by
  norm_num [pairCount, h, CenterCompression.H24.h, Nat.choose]

theorem fixedTarget_counts :
    fixedTargetZero = 210 ∧ fixedTargetOne = 63 ∧ fixedTargetTwo = 3 := by
  norm_num [fixedTargetZero, fixedTargetOne, fixedTargetTwo, h,
    CenterCompression.H24.h, Nat.choose]

theorem fixedTarget_total :
    fixedTargetZero + fixedTargetOne + fixedTargetTwo = pairCount := by
  norm_num [fixedTargetZero, fixedTargetOne, fixedTargetTwo, pairCount, h,
    CenterCompression.H24.h, Nat.choose]

theorem fixedPair_counts :
    fixedPairZero = 1540 ∧ fixedPairOne = 462 ∧ fixedPairTwo = 22 := by
  norm_num [fixedPairZero, fixedPairOne, fixedPairTwo, Nat.choose]

/-- Double-counting target/pair incidences gives the same three totals. -/
theorem target_pair_double_count (c0 c1 c2 : ℕ) :
    targetReadoutCost c0 c1 c2 = pairCount * fixedPairWeight c0 c1 c2 := by
  norm_num [targetReadoutCost, fixedTargetWeight, fixedPairWeight,
    fixedTargetZero, fixedTargetOne, fixedTargetTwo,
    fixedPairZero, fixedPairOne, fixedPairTwo, v, h, pairCount,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose] <;> ring

theorem fixedTargetWeight_two : fixedTargetWeight 2 2 2 = 552 := by
  norm_num [fixedTargetWeight, fixedTargetZero, fixedTargetOne,
    fixedTargetTwo, h, CenterCompression.H24.h, Nat.choose]

theorem targetReadoutCost_two : targetReadoutCost 2 2 2 = 1117248 := by
  norm_num [targetReadoutCost, fixedTargetWeight, fixedTargetZero,
    fixedTargetOne, fixedTargetTwo, v, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem frameSlotCost_two (B : ℕ) :
    frameSlotCost B 2 2 2 = B * 552 := by
  rw [frameSlotCost, fixedTargetWeight_two]

theorem separatedLedgerCost_two (B : ℕ) :
    separatedLedgerCost B 2 2 2 = B * 552 + 1117248 := by
  rw [separatedLedgerCost, frameSlotCost_two, targetReadoutCost_two]

/-- With `B = v²`, the separated ledger is additive, not a `v³` product. -/
theorem separatedLedgerCost_two_at_v_sq :
    separatedLedgerCost (v ^ 2) 2 2 2 = 2262427200 := by
  norm_num [separatedLedgerCost, frameSlotCost, targetReadoutCost,
    fixedTargetWeight, fixedTargetZero, fixedTargetOne, fixedTargetTwo,
    v, h, CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

/-- This is the explicit overcount obtained by multiplying a `v²` block
    and a quantity that already includes the target factor `v`. -/
theorem nested_product_stress_at_v_sq :
    (v ^ 2) * targetReadoutCost 2 2 2 = 4576891342848 := by
  norm_num [targetReadoutCost, fixedTargetWeight, fixedTargetZero,
    fixedTargetOne, fixedTargetTwo, v, h, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

end AllPairCostDecompositionH24
end ExactFourier
end OAI
