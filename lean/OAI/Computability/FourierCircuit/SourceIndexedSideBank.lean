import OAI.Computability.FourierCircuit.CompressedInvocation
import OAI.Computability.FourierCircuit.SourceIndexedSideArithmetic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic

/-!
# Source-indexed side bank

This file checks the scalar source-indexed candidate independently of the
ordered-pair bank.  There is one auxiliary coordinate for each source triple
`T`; the write map is the identity (`V x = x`) and the target-dependent read
map is `sideAction`.  Thus the algebraic identity is exact and the generic
eight-row/inverse/three-invocation certificates apply.

The source index is not a frame label.  The existing row-5 target boundary
requires a common frame for all targets reading a fixed source `T`; the
conditional full-frame penalty and the resulting negative h=24 saving are
recorded in `docs/source-indexed-side-audit.md`.  This module therefore proves
the scalar map and the nominal width, while making no claim that the map is a
frame-compatible circuit in the current schedule.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SourceIndexedSideBank

open CenterCompression
open CompressedInvocation

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

abbrev SideBank (h : ℕ) (K : Type*) := Triple h → K

/- The side bank is indexed only by the source triple. -/
def V (x : Triple h → K) : SideBank h K := x

noncomputable def J (a : SideBank h K) : Triple h → K :=
  fun S => sideAction S a

theorem J_add (a b : SideBank h K) : J (a + b) = J a + J b := by
  classical
  funext S
  unfold J sideAction
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [mul_add]

noncomputable def JHom : SideBank h K →+ (Triple h → K) where
  toFun := J
  map_zero' := by
    classical
    funext S
    simp [J, sideAction]
  map_add' := J_add

noncomputable def RHom : (Fin h → K) →+ (Triple h → K) where
  toFun := fun c S => compressedR S c
  map_zero' := by
    funext S
    simp [compressedR]
  map_add' := by
    intro a b
    funext S
    simp [compressedR, Finset.sum_add_distrib, add_div]

theorem JV_eq_sideAction (x : Triple h → K) (S : Triple h) :
    J (V x) S = sideAction S x := by
  rfl

/- The centre compression and source-indexed side readout form an identity. -/
theorem identity (x : Triple h → K) :
    RHom (compressedG x) + JHom (V x) = x := by
  funext S
  change compressedR S (compressedG x) + sideAction S x = x S
  exact compressed_plus_side S x

abbrev State (h : ℕ) (K : Type*) :=
  CompressedInvocation.State (Triple h → K) (SideBank h K) (Fin h → K)

theorem compressed_restore (s : State h K) :
    eightRows RHom compressedG JHom V s = { s with y := s.y + s.x } := by
  exact @eightRows_restore (Triple h → K) (SideBank h K) (Fin h → K) _ _ _
    RHom compressedG JHom V identity s

theorem compressed_inverse_restore (s : State h K) :
    inverseEightRows RHom compressedG JHom V s = { s with y := s.y - s.x } := by
  exact @inverseEightRows_restore (Triple h → K) (SideBank h K) (Fin h → K) _ _ _
    RHom compressedG JHom V identity s

theorem compressed_exchange (s : State h K) :
    threeInvocations RHom compressedG JHom V s = { s with x := -s.y, y := s.x } := by
  exact @threeInvocations_exchange (Triple h → K) (SideBank h K) (Fin h → K) _ _ _
    RHom compressedG JHom V identity s

namespace H24

open SourceIndexedSideArithmetic.H24

def penalty : ℕ := 2 * I0 * v
def effectiveSaving : ℤ := (centreSaving : ℤ) - penalty

theorem nominal_width_eq : roleCount = 41752302592 := roleCount_eq

theorem nominal_padding_eq : padding = 68719476736 := padding_eq

theorem conditional_penalty_eq : penalty = 49748818944 := by
  norm_num [penalty, I0, v, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem conditional_effective_saving_eq :
    effectiveSaving = -47323645952 := by
  norm_num [effectiveSaving, penalty, centreSaving, I0, v, N0, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

end H24
end SourceIndexedSideBank
end ExactFourier
end OAI
