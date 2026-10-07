import OAI.Computability.FourierCircuit.CompressedInvocation
import OAI.Computability.FourierCircuit.SideMomentFactorization

/-!
# Eight-row invocation with a direct source readout

The moment factorization has a diagonal term `x_S` that cannot be read from
the side bank alone.  This file records the minimal interface extension: a
linear map `K : X → X` is read directly from the immutable source bank in the
two target shears.  The old values are still restored, and the proof is purely
algebraic.  Frame labels and the cost of the direct channel remain separate
obligations.
-/

namespace OAI
namespace ExactFourier
namespace DirectSourceInvocation

open CompressedInvocation

variable {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

def eightRows (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (s : State X A C) : State X A C :=
  let s0 := { s with y := s.y - J s.side }
  let s1 := { s0 with y := s0.y - R s0.center }
  let s2 := { s1 with side := s1.side + V s1.x }
  let s3 := { s2 with center := s2.center + G s2.x }
  let s4 := { s3 with y := s3.y + R s3.center }
  let s5 := { s4 with y := s4.y + J s4.side + K s4.x }
  let s6 := { s5 with center := s5.center - G s5.x }
  { s6 with side := s6.side - V s6.x }

theorem eightRows_restore (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (hidentity : ∀ x, R (G x) + J (V x) + K x = x)
    (s : State X A C) :
    eightRows R G J V K s = { s with y := s.y + s.x } := by
  cases s with
  | mk x y a c =>
    simp only [eightRows, map_add]
    have hy : y - J a - R c + (R c + R (G x)) +
        (J a + J (V x)) + K x = y + x := by
      calc
        _ = y + (R (G x) + J (V x) + K x) := by abel
        _ = y + x := by rw [hidentity]
    simp only [hy, add_sub_cancel_right]

def inverseEightRows (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (s : State X A C) : State X A C :=
  let s0 := { s with side := s.side + V s.x }
  let s1 := { s0 with center := s0.center + G s0.x }
  let s2 := { s1 with y := s1.y - J s1.side - K s1.x }
  let s3 := { s2 with y := s2.y - R s2.center }
  let s4 := { s3 with center := s3.center - G s3.x }
  let s5 := { s4 with side := s4.side - V s4.x }
  let s6 := { s5 with y := s5.y + R s5.center }
  { s6 with y := s6.y + J s6.side }

theorem inverseEightRows_restore
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (hidentity : ∀ x, R (G x) + J (V x) + K x = x)
    (s : State X A C) :
    inverseEightRows R G J V K s = { s with y := s.y - s.x } := by
  cases s with
  | mk x y a c =>
    simp only [inverseEightRows, map_add, add_sub_cancel_right]
    have hy : y - (J a + J (V x)) - K x - (R c + R (G x)) +
        R c + J a = y - x := by
      calc
        _ = y - (R (G x) + J (V x) + K x) := by abel
        _ = y - x := by rw [hidentity]
    rw [hy]

theorem inverseEightRows_eightRows
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (hidentity : ∀ x, R (G x) + J (V x) + K x = x)
    (s : State X A C) :
    inverseEightRows R G J V K (eightRows R G J V K s) = s := by
  rw [eightRows_restore R G J V K hidentity,
    inverseEightRows_restore R G J V K hidentity]
  cases s
  simp

def threeInvocations (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (s : State X A C) : State X A C :=
  let s1 := eightRows R G J V K s
  let s2 := { s1 with x := s1.y, y := s1.x }
  let s3 := inverseEightRows R G J V K s2
  let s4 := { s3 with x := s3.y, y := s3.x }
  eightRows R G J V K s4

theorem threeInvocations_exchange
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (K : X →+ X) (hidentity : ∀ x, R (G x) + J (V x) + K x = x)
    (s : State X A C) :
    threeInvocations R G J V K s = { s with x := -s.y, y := s.x } := by
  cases s with
  | mk x y a c =>
    simp only [threeInvocations, eightRows_restore R G J V K hidentity,
      inverseEightRows_restore R G J V K hidentity]
    abel

namespace MomentCandidate

open CenterCompression SideMomentFactorization

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

abbrev MomentBank (h : ℕ) (K : Type*) := K × (Fin h → K)

noncomputable def VMoment : (Triple h → K) →+ MomentBank h K where
  toFun x := (sideMoment0 x, sideMoment1 x)
  map_zero' := by
    classical
    apply Prod.ext
    · simp [sideMoment0]
    · funext i
      simp [sideMoment1]
  map_add' x y := by
    classical
    apply Prod.ext
    · change sideMoment0 (x + y) = sideMoment0 x + sideMoment0 y
      unfold sideMoment0
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib]
    · funext i
      change sideMoment1 (x + y) i = sideMoment1 x i + sideMoment1 y i
      unfold sideMoment1
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hi : i ∈ T.1 <;> simp [hi]

noncomputable def JNoDiag : MomentBank h K →+ (Triple h → K) where
  toFun a := fun S => (a.1 - ∑ i ∈ S.1, a.2 i) / 2
  map_zero' := by
    classical
    funext S
    simp
  map_add' a b := by
    classical
    funext S
    change (a.1 + b.1 - ∑ i ∈ S.1, (a.2 i + b.2 i)) / 2 =
      (a.1 - ∑ i ∈ S.1, a.2 i) / 2 +
        (b.1 - ∑ i ∈ S.1, b.2 i) / 2
    rw [Finset.sum_add_distrib]
    ring

noncomputable def RHom : (Fin h → K) →+ (Triple h → K) where
  toFun := fun c S => compressedR S c
  map_zero' := by
    funext S
    simp [compressedR]
  map_add' := by
    intro a b
    funext S
    simp [compressedR, Finset.sum_add_distrib, add_div]

def KId : (Triple h → K) →+ (Triple h → K) := AddMonoidHom.id _

theorem moment_identity (x : Triple h → K) :
    RHom (compressedG (K := K) x) +
      JNoDiag (VMoment x) + KId x = x := by
  funext S
  change compressedR S (compressedG (K := K) x) +
      SideMomentFactorization.sideMomentNoDiag S x + x S = x S
  exact SideMomentFactorization.compressed_plus_moment_noDiag_direct S x

abbrev State (h : ℕ) (K : Type*) :=
  CompressedInvocation.State (Triple h → K) (MomentBank h K) (Fin h → K)

theorem moment_restore (s : State h K) :
    eightRows RHom compressedG JNoDiag VMoment KId s =
      { s with y := s.y + s.x } := by
  have hid : ∀ x : Triple h → K,
      RHom (compressedG (K := K) x) + JNoDiag (VMoment x) + KId x = x := by
    intro x
    exact moment_identity x
  exact @eightRows_restore (Triple h → K) (MomentBank h K) (Fin h → K) _ _ _
    RHom compressedG JNoDiag VMoment KId hid s

theorem moment_inverse_restore (s : State h K) :
    inverseEightRows RHom compressedG JNoDiag VMoment KId s =
      { s with y := s.y - s.x } := by
  have hid : ∀ x : Triple h → K,
      RHom (compressedG (K := K) x) + JNoDiag (VMoment x) + KId x = x := by
    intro x
    exact moment_identity x
  exact @inverseEightRows_restore (Triple h → K) (MomentBank h K) (Fin h → K) _ _ _
    RHom compressedG JNoDiag VMoment KId hid s

theorem moment_exchange (s : State h K) :
    threeInvocations RHom compressedG JNoDiag VMoment KId s =
      { s with x := -s.y, y := s.x } := by
  have hid : ∀ x : Triple h → K,
      RHom (compressedG (K := K) x) + JNoDiag (VMoment x) + KId x = x := by
    intro x
    exact moment_identity x
  exact @threeInvocations_exchange (Triple h → K) (MomentBank h K) (Fin h → K) _ _ _
    RHom compressedG JNoDiag VMoment KId hid s

end MomentCandidate

end DirectSourceInvocation
end ExactFourier
end OAI
