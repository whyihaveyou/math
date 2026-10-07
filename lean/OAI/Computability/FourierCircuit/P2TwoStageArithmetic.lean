import Mathlib.Tactic

/-!
# p = 2 arithmetic and the terminal-correction obstruction

For two tensor factors, keeping the ordered-pair invocation and the existing
centre-compressed stage accounting gives

`v = choose h 3`, `d = choose (h-3) 3 + 3 (h-3)`,
`N = v^2`, `I = 2v`, and `W = 2N + I (v d + h)`.

The two monotone stages have scalar saving
`Delta = 2N - 2I h^2`.  Their scalar product is
`L S (x,y) = (-y,x+y)`, so a final `S` shear is needed for the rotation
`(-y,x)`.  In the existing terminal labels, this final gate must lift each
exceptional `Y` wire from `U_d^⊥` to the full frame and then return to
`U_d^⊥`, costing two residual dimensions per bank entry, i.e. `2N`.
Consequently the effective margin is `Delta - 2N = -2 I h^2`.

This file only certifies the arithmetic; the frame statement is the direct
terminal-label consequence of the stage labels in explicit.txt, §2.3.
-/

namespace FFT130
namespace P2TwoStage

def v (h : ℕ) : ℕ := Nat.choose h 3
def dNbr (h : ℕ) : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)
def nBank (h : ℕ) : ℕ := v h * v h
def invocations (h : ℕ) : ℕ := 2 * v h
def width (h : ℕ) : ℕ := h * h
def scalarWidth (h : ℕ) : ℕ :=
  2 * nBank h + invocations h * (v h * dNbr h + h)
def scalarDelta (h : ℕ) : ℕ :=
  2 * nBank h - 2 * (invocations h * width h)
def terminalPenalty (h : ℕ) : ℕ := 2 * nBank h
def effectiveDelta (h : ℕ) : ℤ :=
  (scalarDelta h : ℤ) - (terminalPenalty h : ℤ)

theorem h17_values :
    v 17 = 680 ∧ dNbr 17 = 406 ∧ nBank 17 = 462400 ∧
      invocations 17 = 1360 ∧ width 17 = 289 ∧
      scalarWidth 17 = 376416720 ∧ scalarDelta 17 = 138720 ∧
      terminalPenalty 17 = 924800 ∧ effectiveDelta 17 = -786080 := by
  norm_num [v, dNbr, nBank, invocations, width, scalarWidth,
    scalarDelta, terminalPenalty, effectiveDelta, Nat.choose]

theorem h20_values :
    v 20 = 1140 ∧ dNbr 20 = 731 ∧ nBank 20 = 1299600 ∧
      invocations 20 = 2280 ∧ width 20 = 400 ∧
      scalarWidth 20 = 1902660000 ∧ scalarDelta 20 = 775200 ∧
      terminalPenalty 20 = 2599200 ∧ effectiveDelta 20 = -1824000 := by
  norm_num [v, dNbr, nBank, invocations, width, scalarWidth,
    scalarDelta, terminalPenalty, effectiveDelta, Nat.choose]

theorem effectiveDelta_formula (h : ℕ)
    (hbase : 2 * (invocations h * width h) ≤ 2 * nBank h) :
    effectiveDelta h = -(2 * (invocations h * width h) : ℤ) := by
  unfold effectiveDelta scalarDelta terminalPenalty
  have hcast :
      ((2 * nBank h - 2 * (invocations h * width h) : ℕ) : ℤ) =
        (2 * nBank h : ℤ) - (2 * (invocations h * width h) : ℤ) := by
    rw [Nat.cast_sub hbase]
    push_cast
    ring
  rw [hcast]
  push_cast
  ring

end P2TwoStage
end FFT130
