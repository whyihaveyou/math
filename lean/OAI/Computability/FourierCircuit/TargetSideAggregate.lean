import OAI.Computability.FourierCircuit.CenterMap

/-!
# Target-indexed aggregate side correction

The ordered side roles can be replaced algebraically by one aggregate per
target triple.  This file proves the finite scalar update identity and records
the resulting `h = 24` parameter count.  It deliberately does not claim the
full eight-row frame-labelled circuit; the frame obligations are a separate
certificate.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterCompression

def targetAggregateOutput {h : ℕ} {K : Type*} [Field K]
    (S : Triple h) (y x : Triple h → K)
    (a : Triple h → K) (c : Fin h → K) : K :=
  ((y S - a S - compressedR S c) +
      compressedR S (fun i => c i + compressedG (K := K) x i)) +
    (a S + sideAction S x)

theorem targetAggregateOutput_eq
    {h : ℕ} {K : Type*} [Field K] [CharZero K]
    (S : Triple h) (y x : Triple h → K)
    (a : Triple h → K) (c : Fin h → K) :
    targetAggregateOutput S y x a c = y S + x S := by
  unfold targetAggregateOutput
  have hR : compressedR S (fun i => c i + compressedG (K := K) x i) =
      compressedR S c + compressedR S (compressedG (K := K) x) := by
    unfold compressedR
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hR]
  have hmain := compressed_plus_side (S := S) (x := x)
  rw [hmain]
  ring

namespace H24

def Wtarget : ℕ := 2 * N0 + I0 * (v + h)
def WtargetStar : ℕ := 2 ^ 36
def deltaTarget : ℕ := 2 * N0 - 2 * I0 * h ^ 2
def epsilonTarget : ℚ :=
  (deltaTarget : ℚ) / ((m : ℚ) * (WtargetStar : ℚ))

theorem Wtarget_eq : Wtarget = 41752302592 := by
  norm_num [Wtarget, N0, I0, v, h, dNbr, Nat.choose]

theorem WtargetStar_eq : WtargetStar = 68719476736 := by
  norm_num [WtargetStar]

theorem deltaTarget_eq : deltaTarget = 2425172992 := by
  norm_num [deltaTarget, N0, I0, v, h, Nat.choose]

theorem Wtarget_bounds : 2 ^ 35 < Wtarget ∧ Wtarget ≤ WtargetStar := by
  norm_num [Wtarget, WtargetStar, N0, I0, v, h, Nat.choose]

theorem epsilonTarget_eq :
    epsilonTarget = 2368333 / 927712935936 := by
  norm_num [epsilonTarget, deltaTarget, WtargetStar, m, N0, I0, v, h,
    Nat.choose]

theorem epsilonTarget_gt_255e_minus_8 :
    (255 : ℚ) / 10 ^ 8 < epsilonTarget := by
  rw [epsilonTarget_eq]
  norm_num

end H24
end CenterCompression
end ExactFourier
end OAI
