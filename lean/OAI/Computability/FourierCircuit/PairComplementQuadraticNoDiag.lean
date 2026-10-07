import Mathlib.Tactic

/-!
# Quadratic no-diagonal certificate for pair moments

Pair/complement and global moments have coefficients which are quadratic in
the intersection number `r = |S ∩ T|`.  The three off-diagonal values needed
to cancel the compressed coefficient force the fourth (diagonal) value, so a
direct diagonal bank cannot be removed by the same moments.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementQuadraticNoDiag

def coefficient (a b c r : ℚ) : ℚ :=
  a + b * r + c * (r * (r - 1) / 2)

theorem forced_diagonal (a b c : ℚ)
    (h0 : coefficient a b c 0 = (1 : ℚ) / 2)
    (h1 : coefficient a b c 1 = 0)
    (h2 : coefficient a b c 2 = -(1 : ℚ) / 2) :
    coefficient a b c 3 = -1 := by
  dsimp [coefficient] at h0 h1 h2 ⊢
  linarith

theorem no_diagonal_free_quadratic (a b c : ℚ)
    (h0 : coefficient a b c 0 = (1 : ℚ) / 2)
    (h1 : coefficient a b c 1 = 0)
    (h2 : coefficient a b c 2 = -(1 : ℚ) / 2)
    (h3 : coefficient a b c 3 = 0) :
    False := by
  have hforced := forced_diagonal a b c h0 h1 h2
  linarith

end PairComplementQuadraticNoDiag
end ExactFourier
end OAI
