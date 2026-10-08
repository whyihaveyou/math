import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-! Conditional arithmetic only: a parameterised one-boundary fused-centre ledger.

The definitions below isolate the arithmetic hypothesis used by the finite
stress tests.  They make no claim that a frame-labelled gate schedule realizes
the ledger or that it extends to an all-length recursion.
-/
namespace OAI.ExactFourier.FusedCentreBoundaryGeneral

def value (h : ℕ) : ℕ := Nat.choose h 3
def baseCount (h : ℕ) : ℕ := value h ^ 3
def incidenceCount (h : ℕ) : ℕ := 3 * value h ^ 2
def fusedSaving (h : ℕ) : ℕ :=
  2 * baseCount h - 4 * value h ^ 2 * h ^ 2
def shearCharge (h : ℕ) : ℕ := incidenceCount h * h
def fusedMargin (h : ℕ) : ℤ :=
  (fusedSaving h : ℤ) - (shearCharge h : ℤ)
def normalized (h padding : ℕ) : ℚ :=
  (fusedMargin h : ℚ) / ((h ^ 3 : ℕ) : ℚ) / (padding : ℚ)

/- A reusable endpoint lemma: once the integer margin and positive dimensions
are supplied, the normalized claim is a plain rational inequality. -/
theorem normalized_gt_one_e_minus_nine_of_values
    (h padding margin : ℕ)
    (hm : fusedMargin h = margin)
    (hh : 0 < h) (hp : 0 < padding)
    (bound : (h : ℚ) ^ 3 * padding < (margin : ℚ) * 10 ^ 9) :
    (1 : ℚ) / 10 ^ 9 < normalized h padding := by
  unfold normalized
  rw [hm]
  norm_num [show (h ^ 3 : ℕ) = h ^ 3 by rfl]
  field_simp
  nlinarith

/- Exact finite endpoint instantiations.  The positivity is conditional on the
fused-centre ledger encoded above, and does not assert a circuit construction. -/
theorem h18_normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 18 (2 ^ 40) := by
  norm_num [normalized, fusedMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

theorem h24_normalized_gt_one_e_minus_nine :
    (1 : ℚ) / 10 ^ 9 < normalized 24 (2 ^ 45) := by
  norm_num [normalized, fusedMargin, fusedSaving, shearCharge, baseCount,
    incidenceCount, value, Nat.choose]

end OAI.ExactFourier.FusedCentreBoundaryGeneral
