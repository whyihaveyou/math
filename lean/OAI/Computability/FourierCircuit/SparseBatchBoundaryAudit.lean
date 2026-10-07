import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import OAI.Computability.FourierCircuit.CenterBoundaryShearCandidate
import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Sparse batching and modified-boundary audit

This file isolates two conditional checks for side-wire compression.

* For a fixed pair `F`, the source span used by a target `insert k F` is the
  span of the pair labels with the target coordinate removed.  The common
  intersection over all possible target coordinates is zero.  Therefore a
  target-dependent batching scheme cannot reuse one nonzero pair-prefix
  direction across every target; it must either split the batches or add a
  new transport/boundary.
* The local shear repairs the missing target line at the old boundary, but a
  naive boundary change which simply adds that raw line makes the active
  target frame top.  Even charging one direction per target and invocation
  already exceeds the h=24 centre saving.  This is an arithmetic conditional
  no-go for that boundary redesign, not a lower bound for a different gate.

No statement here rules out a redesigned non-common boundary or a circuit
whose cancellations are not represented by these pair-prefix spans.
-/

namespace OAI
namespace ExactFourier
namespace SparseBatchBoundaryAudit

open PairTargetFrameLocal
open CenterCompression
open CenterBoundaryShearCandidate
open SideRowGeneralArbitrary

abbrev K := ZMod 2
abbrev V (h : ℕ) := Fin h → K

/-! ## Target-dependent pair-prefix batching -/

def sharedPairDirection {h : ℕ} (F : Finset (Fin h)) (x : V h) : Prop :=
  ∀ k : Fin h, k ∉ F → x ∈ sourceSpan F k

theorem sharedPairDirection_eq_zero {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) (x : V h)
    (hx : sharedPairDirection F x) : x = 0 := by
  exact common_sourceSpan_eq_bot F hF hh x hx

theorem sharedPairDirection_subsingleton {h : ℕ} (F : Finset (Fin h))
    (hF : F.card = 2) (hh : 4 ≤ h) :
    Subsingleton {x : V h // sharedPairDirection F x} := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : (x : V h) = 0 := sharedPairDirection_eq_zero F hF hh x.1 x.2
  have hy : (y : V h) = 0 := sharedPairDirection_eq_zero F hF hh y.1 y.2
  exact hx.trans hy.symm

/- A linear map whose every output is reusable for all target coordinates is
   necessarily zero.  This is the form used by a batched auxiliary wire. -/
theorem range_sharedPairDirection_eq_bot
    {h : ℕ} {A : Type*} [AddCommGroup A] [Module K A]
    (F : Finset (Fin h)) (hF : F.card = 2) (hh : 4 ≤ h)
    (L : A →ₗ[K] V h)
    (hL : ∀ a, sharedPairDirection F (L a)) :
    LinearMap.range L = ⊥ := by
  apply le_antisymm
  · rintro z ⟨a, rfl⟩
    have hz : L a = 0 := sharedPairDirection_eq_zero F hF hh (L a) (hL a)
    rw [hz]
    exact Submodule.zero_mem _
  · exact bot_le

namespace H24

def pair : Finset (Fin 24) := {0, 1}

theorem pair_card : pair.card = 2 := by
  norm_num [pair]

theorem pair_shared_batch_zero (x : V 24)
    (hx : sharedPairDirection pair x) : x = 0 := by
  exact sharedPairDirection_eq_zero pair pair_card (by norm_num) x hx

/-! ## Naive raw-target boundary enlargement -/

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed

/- One active residual direction per target and invocation, one-way only. -/
def oneWayRawTargetPenalty : ℕ := I0 * v
def oneWayRawTargetMargin : ℤ :=
  (centreSaving : ℤ) - (oneWayRawTargetPenalty : ℤ)

theorem oneWayRawTargetPenalty_eq : oneWayRawTargetPenalty = 24874409472 := by
  norm_num [oneWayRawTargetPenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem oneWayRawTargetMargin_eq : oneWayRawTargetMargin = -22449236480 := by
  norm_num [oneWayRawTargetMargin, centreSaving, oneWayRawTargetPenalty,
    CenterCompression.H24.deltaCompressed, I0, v,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem oneWayRawTargetMargin_neg : oneWayRawTargetMargin < 0 := by
  rw [oneWayRawTargetMargin_eq]
  norm_num

theorem raw_target_boundary_full
    {ι : Type*} [Fintype ι] {h : ℕ}
    (p : ι → K) (t : Fin h → K)
    (ht : dotProduct t t = (1 : K)) :
    (targetPerp t ⊔ (K ∙ t)).comap
        (SideRowGeneralArbitrary.projectP p) = ⊤ := by
  exact full_target_frame_eq_top p t ht

end H24
end SparseBatchBoundaryAudit
end ExactFourier
end OAI
