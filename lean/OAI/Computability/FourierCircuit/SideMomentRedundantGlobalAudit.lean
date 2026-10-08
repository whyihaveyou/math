import OAI.Computability.FourierCircuit.SideMomentFactorization
import OAI.Computability.FourierCircuit.SideMomentArithmetic
import OAI.Computability.FourierCircuit.CompressedInvocation
import Mathlib.Tactic

/-!
# Redundant global moment in the side-moment factorization

For a triple source bank, the global moment `q = sum_T x_T` is already
determined by the incidence moments:

`sum_i a_i = 3 q`.

Over a characteristic-zero field we may therefore replace `q` by one third of
the incidence sum.  This removes one auxiliary side coordinate while keeping
the scalar identity exact.  At `h = 24` the role count crosses from `2^35` to
`2^34`, giving a conditional normalized width margin just above `10^-5`.

The theorem is deliberately an algebraic audit.  It does not implement the
direct `x_S` term in a frame-preserving complex gate, and it does not supply a
global schedule or an all-length DFT recurrence.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SideMomentRedundantGlobalAudit

open CenterCompression
open SideMomentFactorization

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

def incidenceTotal (x : Triple h → K) : K :=
  ∑ i : Fin h, sideMoment1 x i

theorem incidenceTotal_eq_three_mul_global (x : Triple h → K) :
    incidenceTotal x = 3 * sideMoment0 x := by
  unfold incidenceTotal sideMoment0 sideMoment1
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    (∑ x_1 : Fin h, if x_1 ∈ T.1 then x T else 0) =
        (∑ x_1 : Fin h, if x_1 ∈ T.1 then (1 : K) else 0) * x T := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hit : i ∈ T.1 <;> simp [hit]
    _ = (3 : K) * x T := by
      have hcard := triple_card T
      simp [hcard]

def sideMomentNoGlobal (S : Triple h) (x : Triple h → K) : K :=
  ((1 / (3 : K)) * incidenceTotal x -
      ∑ i ∈ S.1, sideMoment1 x i) / 2

theorem sideMomentNoGlobal_eq_noDiag (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobal S x = sideMomentNoDiag S x := by
  unfold sideMomentNoGlobal sideMomentNoDiag
  rw [incidenceTotal_eq_three_mul_global]
  field_simp

theorem compressed_plus_noGlobal_direct (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) +
        sideMomentNoGlobal S x + x S = x S := by
  rw [sideMomentNoGlobal_eq_noDiag]
  exact compressed_plus_moment_noDiag_direct S x

/-! ## Algebraic direct-input extension

The usual `CompressedInvocation.eightRows` interface gives `J` access only to
the side bank.  The following variant adds a separately supplied direct map
`D : X →+ X` at the target row.  It restores the arbitrary side and centre
banks exactly when `R G + J V + D = id`.  This is an algebraic interface
certificate; a physical frame schedule for the direct row remains open.
-/

def eightRowsDirect
    {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A) (D : X →+ X)
    (s : _root_.OAI.ExactFourier.CompressedInvocation.State X A C) :
    _root_.OAI.ExactFourier.CompressedInvocation.State X A C :=
  let s0 := { s with y := s.y - J s.side }
  let s1 := { s0 with y := s0.y - R s0.center }
  let s2 := { s1 with side := s1.side + V s1.x }
  let s3 := { s2 with center := s2.center + G s2.x }
  let s4 := { s3 with y := s3.y + R s3.center }
  let s5 := { s4 with y := s4.y + J s4.side }
  let s6 := { s5 with y := s5.y + D s5.x }
  let s7 := { s6 with center := s6.center - G s6.x }
  { s7 with side := s7.side - V s7.x }

theorem eightRowsDirect_restore
    {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A) (D : X →+ X)
    (hidentity : ∀ x, R (G x) + J (V x) + D x = x)
    (s : _root_.OAI.ExactFourier.CompressedInvocation.State X A C) :
    eightRowsDirect R G J V D s = { s with y := s.y + s.x } := by
  cases s with
  | mk x y a c =>
    simp only [eightRowsDirect, map_add]
    have hy : y - J a - R c + (R c + R (G x)) + (J a + J (V x)) + D x = y + x := by
      calc
        _ = y + (R (G x) + J (V x) + D x) := by abel
        _ = y + x := by rw [hidentity]
    simp [hy, add_sub_cancel]

namespace H24

abbrev h24 : ℕ := 24
abbrev v : ℕ := CenterCompression.H24.v
abbrev N0 : ℕ := CenterCompression.H24.N0
abbrev I0 : ℕ := CenterCompression.H24.I0
abbrev m : ℕ := CenterCompression.H24.m

/- h incidence side coordinates plus h compressed centre coordinates. -/
def roleCount : ℕ := 2 * N0 + I0 * (h24 + h24)
def padding : ℕ := 2 ^ 34
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def normalized : ℚ :=
  (centreSaving : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem roleCount_eq : roleCount = 17172846592 := by
  norm_num [roleCount, N0, I0, v, h24,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 17179869184 := by
  norm_num [padding]

theorem roleCount_padding_bounds : 2 ^ 33 < roleCount ∧ roleCount ≤ padding := by
  rw [roleCount_eq, padding_eq]
  norm_num

theorem padding_is_strictly_below_previous : padding < 2 ^ 35 := by
  rw [padding_eq]
  norm_num

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem normalized_eq :
    normalized = 2368333 / 231928233984 := by
  rw [normalized, centreSaving_eq, padding_eq]
  norm_num [m, CenterCompression.H24.m, CenterCompression.H24.v,
    CenterCompression.H24.h, CenterCompression.H24.Wstar, Nat.choose]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

theorem normalized_gt_one_e_minus_six :
    (1 : ℚ) / 10 ^ 6 < normalized := by
  rw [normalized_eq]
  norm_num

end H24
end SideMomentRedundantGlobalAudit
end ExactFourier
end OAI
