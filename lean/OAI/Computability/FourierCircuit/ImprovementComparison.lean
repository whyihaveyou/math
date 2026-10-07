import H24lean.CenterCompression

/-!
# Exact comparison with the uncompressed-centre H=24 candidate

The centre compression removes one auxiliary wire per invocation while keeping
all other audited counts fixed.  This module records the exact old and new
multipliers and proves that the compressed candidate has a strictly smaller
recurrence multiplier.  It is an arithmetic comparison only: the missing
frame-labelled invocation proof remains separate.
-/

namespace OAI
namespace ExactFourier
namespace ImprovementComparison
namespace H24

open CenterCompression

def Wbaseline : ℕ := 2 * H24.N0 + H24.I0 * (H24.v * H24.dNbr + H24.h + 1)
def deltaBaseline : ℕ := 2 * H24.N0 - 2 * H24.I0 * H24.h * (H24.h + 1)
def lambdaBaseline : ℚ :=
  (H24.m : ℚ) - (deltaBaseline : ℚ) / H24.Wstar
def lambdaCompressed : ℚ :=
  (H24.m : ℚ) - (H24.deltaCompressed : ℚ) / H24.Wstar

theorem Wbaseline_eq : Wbaseline = 34666942577344 := by
  norm_num [Wbaseline, H24.N0, H24.I0, H24.v, H24.dNbr, H24.h, Nat.choose]

theorem deltaBaseline_eq : deltaBaseline = 1835266048 := by
  norm_num [deltaBaseline, H24.N0, H24.I0, H24.v, H24.h, Nat.choose]

theorem lambdaBaseline_eq :
    lambdaBaseline = 118747255351745 / 8589934592 := by
  norm_num [lambdaBaseline, deltaBaseline, H24.m, H24.Wstar,
    H24.N0, H24.I0, H24.v, H24.h, Nat.choose]

theorem lambdaCompressed_eq :
    lambdaCompressed = 474989020830899 / 34359738368 := by
  norm_num [lambdaCompressed, H24.m, H24.deltaCompressed, H24.Wstar,
    H24.N0, H24.I0, H24.v, H24.h, Nat.choose]

theorem lambda_gap_eq :
    lambdaBaseline - lambdaCompressed = 576081 / 34359738368 := by
  rw [lambdaBaseline_eq, lambdaCompressed_eq]
  norm_num

theorem compressed_multiplier_strictly_better :
    lambdaCompressed < lambdaBaseline := by
  have hgap : 0 < lambdaBaseline - lambdaCompressed := by
    rw [lambda_gap_eq]
    norm_num
  exact sub_pos.mp hgap

end H24
end ImprovementComparison
end ExactFourier
end OAI
