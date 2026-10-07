import Mathlib.Tactic

/-!
# Conditional no-go for the naive fused-terminal redesign

The h = 18 p = 1 arithmetic candidate gains 168 units only because the
terminal bank gate is charged one residual line per Y role.  A natural repair
is to absorb the terminal matrix into repeated restored-auxiliary shears.  A
three-shear exchange is the scalar rotation already proved by
`CompressedInvocation.threeInvocations_exchange`; if it uses the same role
bank and each invocation has the usual h² central decrease, its frame budget
has no positive deficit.

This file is deliberately conditional.  It rules out the naive redesign with
the same physical roles and three ordinary common-frame shears.  It does not
rule out a new gate topology, a non-common-frame operation, or a schedule with
different role labels.
-/

namespace OAI
namespace ExactFourier
namespace FusedTerminalNoGo

def h : ℤ := 18
def N : ℤ := 816

/- Each ordinary p = 1 invocation has h central wires, each losing h
   dimensions once; the absolute-value accounting charges twice this loss. -/
def centralLoss : ℤ := h * h

/- With no separate terminal bank gate, the signed source/sink telescope is
   2N and k repeated invocations pay 2k centralLoss. -/
def fusedDeficit (k : ℤ) : ℤ := 2 * N - 2 * k * centralLoss

theorem h_eq : h = 18 := by rfl

theorem N_eq : N = 816 := by rfl

theorem centralLoss_eq : centralLoss = 324 := by
  norm_num [centralLoss, h]

theorem three_shear_deficit : fusedDeficit 3 = -312 := by
  norm_num [fusedDeficit, centralLoss, h, N]

theorem three_shear_not_positive : fusedDeficit 3 < 0 := by
  norm_num [fusedDeficit, centralLoss, h, N]

/- Two shears would leave a positive arithmetic margin, so the open question
   is genuinely algebraic/frame-topological: one must realize the rotation
   with fewer than the three shears in `threeInvocations_exchange`, or change
   the gate labels.  This theorem records the target without claiming it is
   attainable. -/
theorem two_shear_target_margin : fusedDeficit 2 = 336 := by
  norm_num [fusedDeficit, centralLoss, h, N]

theorem k_shear_deficit_formula (k : ℤ) :
    fusedDeficit k = 1632 - 648 * k := by
  norm_num [fusedDeficit, centralLoss, h, N]
  ring

theorem every_three_or_more_shear_deficit_nonpositive
    {k : ℤ} (hk : 3 ≤ k) : fusedDeficit k ≤ -312 := by
  rw [k_shear_deficit_formula]
  linarith

/- The one-stage candidate's positive margin is exactly the terminal shortcut's
   168 units.  Removing that shortcut while retaining the common-frame bank
   gate incurs the already-audited two-residual boundary. -/
def commonFrameDeficit : ℤ := -648

theorem common_frame_deficit_eq : commonFrameDeficit = -648 := by rfl

theorem common_frame_deficit_lt_fused_three_shear :
    commonFrameDeficit < fusedDeficit 3 := by
  norm_num [fusedDeficit, centralLoss, h, N, commonFrameDeficit]

end FusedTerminalNoGo
end ExactFourier
end OAI
