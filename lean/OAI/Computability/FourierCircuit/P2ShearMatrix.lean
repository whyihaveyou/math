import Mathlib.Tactic

/-! A tiny scalar sanity check: two elementary shears cannot be the Fourier
rotation.  This is independent of the frame construction. -/

namespace FFT130
namespace P2ShearMatrix

def upper (a : ℚ) (z : ℚ × ℚ) : ℚ × ℚ := (z.1, z.2 + a * z.1)
def lower (b : ℚ) (z : ℚ × ℚ) : ℚ × ℚ := (z.1 + b * z.2, z.2)
def rot (z : ℚ × ℚ) : ℚ × ℚ := (-z.2, z.1)

theorem lower_upper_ne_rot (a b : ℚ) :
    (fun z => lower b (upper a z)) ≠ rot := by
  intro h
  have h10 := congrFun h (1, 0)
  have h01 := congrFun h (0, 1)
  simp [lower, upper, rot] at h10 h01

theorem upper_lower_ne_rot (a b : ℚ) :
    (fun z => upper a (lower b z)) ≠ rot := by
  intro h
  have h10 := congrFun h (1, 0)
  have h01 := congrFun h (0, 1)
  simp [lower, upper, rot] at h10 h01

end P2ShearMatrix
end FFT130
