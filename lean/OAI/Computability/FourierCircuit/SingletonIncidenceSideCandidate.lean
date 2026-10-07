import OAI.Computability.FourierCircuit.SideMomentFactorization
import Mathlib.Tactic

open scoped BigOperators

/-!
# Singleton-incidence side identity

The global moment in `SideMomentFactorization` is algebraically redundant: every
source triple contributes to exactly three singleton incidence moments.  This
file proves the redundancy over an arbitrary characteristic-zero field.  It is
an exact scalar identity only; the incidence frame, target-dependent readout,
and physical gate schedule remain separate obligations.
-/

namespace OAI
namespace ExactFourier
namespace SingletonIncidenceSideCandidate

open CenterCompression
open SideMomentFactorization

def sideMomentNoGlobal {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (x : Triple h → K) : K :=
  ((∑ i : Fin h, sideMoment1 x i) / (3 : K) -
      ∑ i ∈ S.1, sideMoment1 x i) / 2

theorem sideMoment1_total
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (x : Triple h → K) :
    (∑ i : Fin h, sideMoment1 x i) =
      (3 : K) * sideMoment0 x := by
  classical
  unfold sideMoment1 sideMoment0
  rw [Finset.sum_comm]
  have hinner : ∀ T : Triple h,
      (∑ i : Fin h, if i ∈ T.1 then x T else 0) =
        (3 : K) * x T := by
    intro T
    calc
      (∑ i : Fin h, if i ∈ T.1 then x T else 0) =
          (∑ i : Fin h, (if i ∈ T.1 then (1 : K) else 0)) * x T := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hit : i ∈ T.1 <;> simp [hit]
      _ = (T.1.card : K) * x T := by
            rw [incidence_sum]
            simp
      _ = (3 : K) * x T := by simp [triple_card T]
  simp_rw [hinner]
  rw [← Finset.mul_sum]

theorem sideMomentNoGlobal_eq_noDiag
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobal S x = sideMomentNoDiag S x := by
  unfold sideMomentNoGlobal sideMomentNoDiag
  rw [sideMoment1_total]
  field_simp

theorem compressed_plus_singleton_noGlobal
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (x : Triple h → K) :
    compressedR S (compressedG (K := K) x) +
        sideMomentNoGlobal S x + x S = x S := by
  rw [sideMomentNoGlobal_eq_noDiag]
  exact SideMomentFactorization.compressed_plus_moment_noDiag_direct S x

namespace H24

abbrev h : ℕ := CenterCompression.H24.h
abbrev v : ℕ := CenterCompression.H24.v
abbrev N0 : ℕ := CenterCompression.H24.N0
abbrev I0 : ℕ := CenterCompression.H24.I0
abbrev m : ℕ := CenterCompression.H24.m

/- Source/target banks, h centre roles and h singleton-incidence side roles. -/
def roleCount : ℕ := 2 * N0 + I0 * (2 * h)
def padding : ℕ := 2 ^ 34
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed
def normalized : ℚ :=
  (centreSaving : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem roleCount_eq : roleCount = 17172846592 := by
  norm_num [roleCount, N0, I0, h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

theorem padding_eq : padding = 17179869184 := by
  norm_num [padding]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem roleCount_bounds : 2 ^ 33 < roleCount ∧ roleCount ≤ padding := by
  norm_num [roleCount, padding, N0, I0, h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

theorem normalized_eq :
    normalized = 2368333 / 231928233984 := by
  norm_num [normalized, centreSaving, padding, m,
    CenterCompression.H24.deltaCompressed, CenterCompression.H24.m,
    CenterCompression.H24.h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v, Nat.choose]

theorem normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized := by
  rw [normalized_eq]
  norm_num

end H24
end SingletonIncidenceSideCandidate
end ExactFourier
end OAI
