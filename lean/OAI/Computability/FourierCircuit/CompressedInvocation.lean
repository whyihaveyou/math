import OAI.Computability.FourierCircuit.CenterMap
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Compressed eight-row invocation with ordered-pair side roles

This file verifies the scalar eight-row state transition, including restoration
of arbitrary auxiliary values. The side bank has a separate coordinate for
each ordered pair of distinct triples with even intersection. There is no
aggregation of side roles. Frame labels, physical gate depth and recursive DFT
assembly are outside the scope of the algebraic transition proved here.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CompressedInvocation

structure State (X A C : Type*) where
  x : X
  y : X
  side : A
  center : C

section Generic

variable {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

/-- The eight rows in their execution order; readouts act on the current bank. -/
def eightRows (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : State X A C) : State X A C :=
  let s0 := { s with y := s.y - J s.side }
  let s1 := { s0 with y := s0.y - R s0.center }
  let s2 := { s1 with side := s1.side + V s1.x }
  let s3 := { s2 with center := s2.center + G s2.x }
  let s4 := { s3 with y := s3.y + R s3.center }
  let s5 := { s4 with y := s4.y + J s4.side }
  let s6 := { s5 with center := s5.center - G s5.x }
  { s6 with side := s6.side - V s6.x }

/- No zero-initialization is needed: both arbitrary auxiliary banks are restored. -/
theorem eightRows_restore (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    eightRows R G J V s = { s with y := s.y + s.x } := by
  cases s with
  | mk x y a c =>
    simp only [eightRows, map_add]
    have hy : y - J a - R c + (R c + R (G x)) + (J a + J (V x)) = y + x := by
      calc
        _ = y + (R (G x) + J (V x)) := by abel
        _ = y + x := by rw [hidentity]
    simp only [hy, add_sub_cancel_right]

/- A three-shear bank exchange; every shear restores the auxiliary banks. -/
def threeInvocations (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : State X A C) : State X A C :=
  let s1 := eightRows R G J V s
  let s2 := { s1 with x := s1.y, y := s1.x }
  let s3 := { s2 with y := s2.y - s2.x }
  let s4 := { s3 with x := s3.y, y := s3.x }
  eightRows R G J V s4

theorem threeInvocations_exchange
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    threeInvocations R G J V s = { s with x := -s.y, y := s.x } := by
  -- Unfolding the bank exchanges and applying the scalar shear law three times.
  cases s with
  | mk x y a c =>
    simp only [threeInvocations, eightRows_restore R G J V hidentity]
    abel

end Generic

namespace OrderedPairs

open CenterCompression

/-- One coordinate for each legal ordered `(target,source)` pair. -/
def Allowed {h : ℕ} (S T : Triple h) : Prop :=
  S ≠ T ∧ Even (S.1 ∩ T.1).card

/- A role stores both endpoints and its legality proof.  This avoids quotienting
   or aggregating side coordinates: each legal ordered pair is independent. -/
structure Role (h : ℕ) where
  target : Triple h
  source : Triple h
  admissible : Allowed target source

abbrev SideBank (h : ℕ) (K : Type*) := Role h → K

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

def V (x : Triple h → K) : SideBank h K := fun r => x r.source

noncomputable def J (a : SideBank h K) : Triple h → K := by
  classical
  exact fun S => ∑ T ∈ (tripleSet h).attach,
    if hST : Allowed S T then sideCoeff S T * a ⟨S, T, hST⟩ else 0

theorem J_add (a b : SideBank h K) : J (a + b) = J a + J b := by
  classical
  funext S
  simp only [J, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  split_ifs <;> simp [mul_add]

noncomputable def JHom : SideBank h K →+ (Triple h → K) where
  toFun := J
  map_zero' := by
    classical
    funext S
    simp [J]
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
  classical
  unfold J sideAction
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hST : Allowed S T
  · simp [hST, V]
  · have hzero : sideCoeff (K := K) S T = 0 := by
      by_cases heq : S = T
      · simp [sideCoeff, heq]
      · have hodd : ¬ Even (S.1 ∩ T.1).card := fun heven => hST ⟨heq, heven⟩
        simp [sideCoeff, heq, hodd]
    simp [hST, hzero]

theorem identity (x : Triple h → K) :
    RHom (compressedG x) + JHom (V x) = x := by
  funext S
  change compressedR S (compressedG x) + J (V x) S = x S
  rw [JV_eq_sideAction]
  exact compressed_plus_side S x

theorem compressed_restore
    (s : State (Triple h → K) (SideBank h K) (Fin h → K)) :
    eightRows RHom compressedG JHom V s = { s with y := s.y + s.x } := by
  exact @eightRows_restore (Triple h → K) (SideBank h K) (Fin h → K) _ _ _
    RHom compressedG JHom V identity s

theorem compressed_exchange
    (s : State (Triple h → K) (SideBank h K) (Fin h → K)) :
    threeInvocations RHom compressedG JHom V s = { s with x := -s.y, y := s.x } := by
  exact @threeInvocations_exchange (Triple h → K) (SideBank h K) (Fin h → K) _ _ _
    RHom compressedG JHom V identity s

end OrderedPairs
end CompressedInvocation
end ExactFourier
end OAI
