import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Centre-wire directional-step audit

This file isolates the dimension bookkeeping for the centre wires after the
global centre coordinate is removed.  It does not construct the full
frame-labelled circuit.  The geometric interpretation is the one in the
paper's stage table: `E = B ⊥ P`, with `P` a unit line, so `dim E = dim B + 1`,
and `dim D = h`.  A centre wire visits `B ⊗ D`, then `E ⊗ D`, returns to
`B ⊗ D`, and ends at `E ⊗ D`.  The return is the sole central decrease.
-/

namespace OAI
namespace ExactFourier
namespace CenterFrameAudit

/- Signed dimension change along one centre wire.  Integers make the decrease
   explicit instead of hiding it in natural-number subtraction. -/
def signedCentreCost (b h : ℤ) : ℤ :=
  b * h + h - h + h

/- Absolute residual sum for the same four nonzero edges. -/
def absoluteCentreCost (b h : ℤ) : ℤ :=
  b * h + h + h + h

theorem signedCentreCost_eq (b h : ℤ) :
    signedCentreCost b h = (b + 1) * h := by
  dsimp [signedCentreCost]
  ring

theorem absoluteCentreCost_eq (b h : ℤ) :
    absoluteCentreCost b h = (b + 3) * h := by
  dsimp [absoluteCentreCost]
  ring

theorem absolute_minus_signed_eq (b h : ℤ) :
    absoluteCentreCost b h - signedCentreCost b h = 2 * h := by
  rw [absoluteCentreCost_eq, signedCentreCost_eq]
  ring

theorem signedCentreCost_eq_sink_dimension
    (b e h : ℤ) (he : e = b + 1) :
    signedCentreCost b h = e * h := by
  rw [signedCentreCost_eq, he]

/- Removing c_* removes one centre role per invocation, while the central
   absolute-cost correction drops by h for each removed role. -/
def originalCentreLoss (I h : ℕ) : ℕ := I * (h + 1) * h
def compressedCentreLoss (I h : ℕ) : ℕ := I * h * h

theorem centre_loss_drop (I h : ℕ) :
    originalCentreLoss I h - compressedCentreLoss I h = I * h := by
  dsimp [originalCentreLoss, compressedCentreLoss]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_sub_cancel_left]

def originalRoleCount (N I v d h : ℕ) : ℕ :=
  2 * N + I * (v * d + h + 1)

def compressedRoleCount (N I v d h : ℕ) : ℕ :=
  2 * N + I * (v * d + h)

theorem role_count_drop (N I v d h : ℕ) :
    originalRoleCount N I v d h - compressedRoleCount N I v d h = I := by
  dsimp [originalRoleCount, compressedRoleCount]
  rw [Nat.mul_add, Nat.mul_one]
  omega

namespace H24

def N : ℕ := CenterCompression.H24.N0
def I : ℕ := CenterCompression.H24.I0
def v : ℕ := CenterCompression.H24.v
def d : ℕ := CenterCompression.H24.dNbr
def h : ℕ := CenterCompression.H24.h
def originalW : ℕ := originalRoleCount N I v d h
def compressedW : ℕ := compressedRoleCount N I v d h

theorem originalW_eq : originalW = 34666942577344 := by
  norm_num [originalW, originalRoleCount, N, I, v, d, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.dNbr,
    CenterCompression.H24.h, Nat.choose]

theorem compressedW_eq : compressedW = 34666930287616 := by
  norm_num [compressedW, compressedRoleCount, N, I, v, d, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.dNbr,
    CenterCompression.H24.h, Nat.choose]

theorem role_drop_eq : originalW - compressedW = 12289728 := by
  norm_num [originalW, compressedW, originalRoleCount,
    compressedRoleCount, N, I, v, d, h, CenterCompression.H24.N0,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.dNbr, CenterCompression.H24.h, Nat.choose]

theorem centre_loss_drop_eq :
    originalCentreLoss I h - compressedCentreLoss I h = 294953472 := by
  norm_num [originalCentreLoss, compressedCentreLoss, I, h,
    CenterCompression.H24.I0, CenterCompression.H24.h,
    CenterCompression.H24.v, Nat.choose]

end H24
end CenterFrameAudit
end ExactFourier
end OAI
