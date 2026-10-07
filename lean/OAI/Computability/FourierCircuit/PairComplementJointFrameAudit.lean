import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic.NormNum

/-!
# Conditional joint-frame audit for the pair/complement candidate

The pair/complement scalar factorization has two global pair banks and only
`552` roles per invocation.  A fixed target gate touches all three inside
pairs and all `210` disjoint pairs.  The accompanying GF(2) script shows that
their all-triple support spans join to the full active factor.  Under the
existing common row-5 boundary, this costs two directional units per target
and invocation.  The arithmetic below records that conditional obstruction;
it is not a lower bound for a redesigned gate schedule.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementJointFrameAudit
namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m
def padding : ℕ := 2 ^ 35
def centreSaving : ℕ := CenterCompression.H24.deltaCompressed

/- One full prefix-direction rise and return per target invocation. -/
def jointPenalty : ℕ := 2 * I0 * v
def jointMargin : ℤ := (centreSaving : ℤ) - (jointPenalty : ℤ)
def jointNormalizedMargin : ℚ :=
  (jointMargin : ℚ) / ((m : ℚ) * (padding : ℚ))

theorem h_eq : h = 24 := by
  rfl

theorem jointPenalty_eq : jointPenalty = 49748818944 := by
  norm_num [jointPenalty, I0, v,
    CenterCompression.H24.I0, CenterCompression.H24.v,
    CenterCompression.H24.h, Nat.choose]

theorem centreSaving_eq : centreSaving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem padding_eq : padding = 34359738368 := by
  norm_num [padding]

theorem jointMargin_eq : jointMargin = -47323645952 := by
  rw [jointMargin, centreSaving_eq, jointPenalty_eq]
  norm_num

theorem jointMargin_neg : jointMargin < 0 := by
  rw [jointMargin_eq]
  norm_num

theorem jointNormalizedMargin_eq :
    jointNormalizedMargin = -23107249 / 231928233984 := by
  rw [jointNormalizedMargin, jointMargin_eq, padding_eq]
  norm_num [m, CenterCompression.H24.m, CenterCompression.H24.h]

theorem jointNormalizedMargin_neg : jointNormalizedMargin < 0 := by
  rw [jointNormalizedMargin_eq]
  norm_num

theorem jointPenalty_exceeds_centreSaving : centreSaving < jointPenalty := by
  rw [centreSaving_eq, jointPenalty_eq]
  norm_num

end H24
end PairComplementJointFrameAudit
end ExactFourier
end OAI
