import OAI.Computability.FourierCircuit.SideMomentRedundantGlobalAudit
import OAI.Computability.FourierCircuit.SideMomentFactorization
import OAI.Computability.FourierCircuit.CenterAllLengthBridge
import Mathlib.Tactic

/-!
# Reusing the compressed centre readout for the diagonal-free side moment

The incidence relation `sum_i a_i = 3 q` gives

`sideMomentNoGlobal S x = (q - sum_{i in S} a_i)/2`.

The already-compressed centre coordinates are `c_i = a_i - q/3`, so their
three-coordinate readout is exactly the negative of this side correction.
Thus the q-free side moment does not need a second `h`-coordinate bank: it can
reuse the existing centre readout.  The remaining diagonal `x S` term still
needs a direct source route; this file makes no claim about its frame cost.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SideMomentCentreReuse

open CenterCompression
open SideMomentFactorization
open SideMomentRedundantGlobalAudit
open CenterAllLengthBridge

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

theorem sideMomentNoGlobal_eq_neg_compressedReadout
    (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobal S x =
      -compressedR S (compressedG (K := K) x) := by
  rw [sideMomentNoGlobal_eq_noDiag]
  have hzero : sideMomentNoDiag S x +
      compressedR S (compressedG (K := K) x) = 0 := by
    rw [add_comm]
    exact compressed_plus_moment_noDiag S x
  exact eq_neg_of_add_eq_zero_left hzero

theorem sideMomentNoGlobal_plus_compressedReadout_eq_zero
    (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobal S x + compressedR S (compressedG (K := K) x) = 0 := by
  rw [sideMomentNoGlobal_eq_neg_compressedReadout]
  abel

/-! ## Finite-prefix attachment to the frame schedule

The frame schedule and the moment identity have different state types: a
schedule index carries only `ZMod 2` labels, whereas the identity takes a
`Triple h → K` signal and a selected `Triple h`.  The following certificate
keeps that boundary explicit.  It attaches an independently supplied family
of moment inputs to each finite schedule index and combines the pointwise
reuse identity with the schedule's existing frame and direction ledgers.
It therefore does not claim that the frame labels generate the moment inputs.
-/

theorem frameTowerSchedule_finite_side_reuse_certificate {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ)
    (signals : ℕ → Triple h → K) (selected : ℕ → Triple h) :
    (∀ k ∈ Finset.range n,
      sideMomentNoGlobal (selected k) (signals k) +
          compressedR (selected k) (compressedG (K := K) (signals k)) = 0) ∧
    schedule.totalCentreSteps hh n = n * h ∧
    schedule.totalSideSteps hh n = n * (h - 2) ∧
    schedule.totalDirectionSteps hh n = n * (2 * h - 2) := by
  refine ⟨?_, schedule.total_centre_steps hh n,
    schedule.total_side_steps hh n, schedule.total_direction_steps hh n⟩
  intro k hk
  exact sideMomentNoGlobal_plus_compressedReadout_eq_zero
    (selected k) (signals k)

/-! ## Conditional direction ledger

The preceding certificate only identifies the q-free side correction with a
readout already present in the centre frame.  The following ledger records
the resulting bookkeeping implication for a finite schedule: the reused
direction total is the centre total, so the auxiliary charge assigned to
reconstructing that q-free side readout is zero.  The residual side-direction
charge is still the schedule's ordinary side count.  This is conditional
ledger arithmetic: `signals` and `selected` are supplied inputs, and no
physical gate map is inferred from their existence.
-/

noncomputable def reusedDirectionSteps {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) : ℕ :=
  schedule.totalCentreSteps hh n

noncomputable def auxiliarySideDirectionCharge {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) : ℕ :=
  schedule.totalDirectionSteps hh n -
    (reusedDirectionSteps schedule hh n + schedule.totalSideSteps hh n)

theorem reusedDirectionSteps_eq {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    reusedDirectionSteps schedule hh n = n * h := by
  exact schedule.total_centre_steps hh n

theorem auxiliarySideDirectionCharge_eq_zero {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    auxiliarySideDirectionCharge schedule hh n = 0 := by
  rw [auxiliarySideDirectionCharge, reusedDirectionSteps_eq,
    schedule.total_direction_steps, schedule.total_side_steps]
  have hfactor : 2 * h - 2 = h + (h - 2) := by omega
  rw [hfactor, Nat.mul_add]
  simp

theorem conditional_side_direction_reduction {h : ℕ}
    (schedule : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    schedule.totalDirectionSteps hh n -
        reusedDirectionSteps schedule hh n = n * (h - 2) := by
  rw [reusedDirectionSteps_eq, schedule.total_direction_steps]
  have hfactor : 2 * h - 2 = h + (h - 2) := by omega
  rw [hfactor, Nat.mul_add]
  simp

namespace H24

abbrev h24 : ℕ := CenterCompression.H24.h
abbrev v : ℕ := CenterCompression.H24.v
abbrev N0 : ℕ := CenterCompression.H24.N0
abbrev I0 : ℕ := CenterCompression.H24.I0
abbrev m : ℕ := CenterCompression.H24.m

/- With the q-free side moment reused from the centre readout, only the `h`
   centre coordinates remain in this auxiliary-bank ledger.  The direct
   diagonal route is intentionally not included here. -/
def reusedRoleCount : ℕ := 2 * N0 + I0 * h24
def reusedPadding : ℕ := 2 ^ 34
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def normalized : ℚ :=
  (centreSaving : ℚ) / ((m : ℚ) * (reusedPadding : ℚ))

theorem reusedRoleCount_eq : reusedRoleCount = 16877893120 := by
  norm_num [reusedRoleCount, N0, I0, h24, v,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.h, CenterCompression.H24.v, Nat.choose]

theorem reusedPadding_eq : reusedPadding = 17179869184 := by
  norm_num [reusedPadding]

theorem reusedRoleCount_in_same_padding_bucket :
    2 ^ 33 < reusedRoleCount ∧ reusedRoleCount ≤ reusedPadding := by
  rw [reusedRoleCount_eq, reusedPadding_eq]
  norm_num

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem normalized_eq :
    normalized = 2368333 / 231928233984 := by
  rw [normalized, centreSaving_eq, reusedPadding_eq]
  norm_num [m, CenterCompression.H24.m, CenterCompression.H24.h]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

end H24
end SideMomentCentreReuse
end ExactFourier
end OAI
