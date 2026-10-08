import OAI.Computability.FourierCircuit.SideMomentRedundantGlobalAudit
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

/-!
# Direct-channel cancellation and its conditional budget obstruction

The fixed q-free side construction is the negative of the compressed centre
readout. Consequently, any direct map that completes their scalar identity is
forced to be the full identity map on the source bank. Its cost cannot be
estimated by a smaller rank complement for this particular construction.

The second part records the consequence of a stated charging premise: if each
full direct coordinate costs at least one frame unit per invocation, then the
`3 v^2` invocations cost at least `3 v^3`, while the entire pre-centre saving is
only `2 v^3`. This is negative for every nonempty parameter, so changing `h`
cannot rescue that route. It is not a lower bound for arbitrary complex
circuits or for a redesigned direct operation with a different charge.

The final h=24 role ledger shares the same incidence features between the
centre and q-free side. The shared bank is algebraically valid, but it does
not supply the frame transport or direct gate required to realize this width.
-/

namespace OAI
namespace ExactFourier
namespace DirectChannelCancellationBudget

open CenterCompression
open SideMomentFactorization
open SideMomentRedundantGlobalAudit

section Algebra

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

/-- The fixed q-free side map cancels the entire compressed centre readout. -/
theorem fixed_qfree_cancellation (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) + sideMomentNoGlobal S x = 0 := by
  rw [sideMomentNoGlobal_eq_noDiag]
  exact compressed_plus_moment_noDiag S x

/-- Any linear direct map completing this particular cancellation is the full
identity, rather than merely a rank-complement map. -/
theorem direct_forced_identity
    (D : (Triple h → K) →ₗ[K] (Triple h → K))
    (hidentity : ∀ (S : Triple h) (x : Triple h → K),
      compressedR S (compressedG (K := K) x) + sideMomentNoGlobal S x +
        D x S = x S) :
    D = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext S
  have hD := hidentity S x
  rw [fixed_qfree_cancellation, zero_add] at hD
  exact hD

/-- In particular the direct map is surjective on the whole source bank. -/
theorem direct_forced_surjective
    (D : (Triple h → K) →ₗ[K] (Triple h → K))
    (hidentity : ∀ (S : Triple h) (x : Triple h → K),
      compressedR S (compressedG (K := K) x) + sideMomentNoGlobal S x +
        D x S = x S) :
    Function.Surjective D := by
  rw [direct_forced_identity D hidentity]
  exact Function.surjective_id

/- A factorized direct bank cannot have a smaller auxiliary rank.  This is
   only a statement about the present additive model: after the fixed
   q-free cancellation, the factorized map is forced to be the identity.
   It makes no claim about arbitrary circuits or a different frame schedule. -/
theorem direct_factorization_finrank_lower_bound
    {R : Type*} [AddCommGroup R] [Module K R]
    [FiniteDimensional K R]
    (U : R →ₗ[K] (Triple h → K))
    (V : (Triple h → K) →ₗ[K] R)
    (hidentity : ∀ (S : Triple h) (x : Triple h → K),
      compressedR S (compressedG (K := K) x) + sideMomentNoGlobal S x +
        (U (V x)) S = x S) :
    Module.finrank K (Triple h → K) ≤ Module.finrank K R := by
  have hUV : U.comp V = LinearMap.id :=
    direct_forced_identity (D := U.comp V) hidentity
  apply LinearMap.finrank_le_finrank_of_injective (f := V)
  intro x y hxy
  have hx : U (V x) = x := by
    have h := congrArg (fun f : (Triple h → K) →ₗ[K] (Triple h → K) => f x) hUV
    simpa using h
  have hy : U (V y) = y := by
    have h := congrArg (fun f : (Triple h → K) →ₗ[K] (Triple h → K) => f y) hUV
    simpa using h
  calc
    x = U (V x) := hx.symm
    _ = U (V y) := by rw [hxy]
    _ = y := hy

end Algebra

section Budget

/-- The same natural-number centre saving used in the parameter ledgers. -/
def centreSaving (h v : ℕ) : ℕ := 2 * v ^ 3 - 6 * v ^ 2 * h ^ 2

/-- One unit per direct coordinate in each of the `3 v^2` invocations. -/
def oneWayDirectCharge (v : ℕ) : ℕ := 3 * v ^ 2 * v

def directMargin (h v : ℕ) : ℤ :=
  (centreSaving h v : ℤ) - (oneWayDirectCharge v : ℤ)

/-- Exact direct-charge count, independent of the centre parameter. -/
theorem oneWayDirectCharge_eq (v : ℕ) : oneWayDirectCharge v = 3 * v ^ 3 := by
  unfold oneWayDirectCharge
  ring

/-- A one-unit direct charge already exceeds even the uncharged base saving. -/
theorem base_saving_lt_oneWayDirectCharge (v : ℕ) (hv : 0 < v) :
    2 * v ^ 3 < oneWayDirectCharge v := by
  rw [oneWayDirectCharge_eq]
  have hcube : 0 < v ^ 3 := pow_pos hv 3
  omega

/-- Thus the exact clipped centre saving is insufficient for every `h`. -/
theorem centreSaving_lt_oneWayDirectCharge (h v : ℕ) (hv : 0 < v) :
    centreSaving h v < oneWayDirectCharge v := by
  exact lt_of_le_of_lt (Nat.sub_le _ _) (base_saving_lt_oneWayDirectCharge v hv)

/-- Optimizing `h` cannot make this fixed one-unit direct route positive. -/
theorem directMargin_neg (h v : ℕ) (hv : 0 < v) : directMargin h v < 0 := by
  have hlt : (centreSaving h v : ℤ) < (oneWayDirectCharge v : ℤ) := by
    exact_mod_cast centreSaving_lt_oneWayDirectCharge h v hv
  unfold directMargin
  omega

/-- An implementation charged at least one unit per direct channel also loses
its entire saving. The lower bound `hcharge` is deliberately explicit. -/
theorem charged_direct_margin_neg (h v charge : ℕ) (hv : 0 < v)
    (hcharge : oneWayDirectCharge v ≤ charge) :
    (centreSaving h v : ℤ) - (charge : ℤ) < 0 := by
  have hlt := lt_of_lt_of_le (centreSaving_lt_oneWayDirectCharge h v hv) hcharge
  have hltZ : (centreSaving h v : ℤ) < (charge : ℤ) := by exact_mod_cast hlt
  omega

end Budget

namespace H24

abbrev h24 : ℕ := 24
abbrev v : ℕ := CenterCompression.H24.v
abbrev N0 : ℕ := CenterCompression.H24.N0
abbrev I0 : ℕ := CenterCompression.H24.I0

/-- One shared incidence bank replaces separate h-dimensional centre/side banks. -/
def sharedRoleCount : ℕ := 2 * N0 + I0 * h24
def padding : ℕ := 2 ^ 34

theorem sharedRoleCount_eq : sharedRoleCount = 16877893120 := by
  norm_num [sharedRoleCount, N0, I0, v, h24,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem sharedRoleCount_padding_bounds :
    2 ^ 33 < sharedRoleCount ∧ sharedRoleCount ≤ padding := by
  rw [sharedRoleCount_eq, padding]
  norm_num

theorem sharedBank_saves_one_incidence_copy :
    SideMomentRedundantGlobalAudit.H24.roleCount - sharedRoleCount = 294953472 := by
  rw [SideMomentRedundantGlobalAudit.H24.roleCount_eq, sharedRoleCount_eq]

theorem sharedBank_does_not_change_padding :
    padding = SideMomentRedundantGlobalAudit.H24.padding := by rfl

theorem direct_charge_eq : oneWayDirectCharge v = 24874409472 := by
  rw [oneWayDirectCharge_eq]
  norm_num [v, CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem centre_saving_eq : centreSaving h24 v = 2425172992 := by
  norm_num [centreSaving, h24, v, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem direct_margin_eq : directMargin h24 v = -22449236480 := by
  unfold directMargin
  rw [direct_charge_eq, centre_saving_eq]
  norm_num

end H24
end DirectChannelCancellationBudget
end ExactFourier
end OAI
