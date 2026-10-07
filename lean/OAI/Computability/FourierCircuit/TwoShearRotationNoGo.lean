import Mathlib.Tactic

/-!
# Two-shear matrix-word obstruction

The arithmetic audit leaves a tempting target: if the terminal bank matrix
could be fused into only two ordinary shears, the h = 18 budget would have a
deficit of 336.  This file checks that this cannot happen in the elementary
matrix model.  A shear may update either coordinate, with an arbitrary
integer coefficient, and arbitrary bank swaps may be inserted before,
between, and after the two shears.  Since swaps square to the identity, one
Boolean records each possible swap placement.  No word in this class is the
rotation `[[0,-1],[1,0]]`.

The result is a matrix-word statement only.  It allows a new terminal gate or
other non-elementary operation; it therefore does not rule out redesigns that
leave the shear-plus-swap model.
-/

namespace OAI
namespace ExactFourier
namespace TwoShearRotationNoGo

structure M2 where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ

def one : M2 := ⟨1, 0, 0, 1⟩
def swap : M2 := ⟨0, 1, 1, 0⟩
def e21 (t : ℂ) : M2 := ⟨1, 0, t, 1⟩
def e12 (t : ℂ) : M2 := ⟨1, t, 0, 1⟩
def rotation : M2 := ⟨0, -1, 1, 0⟩

def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d,
    x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def maybeSwap (p : Bool) : M2 := if p then swap else one

def shear (orientation : Bool) (t : ℂ) : M2 :=
  if orientation then e12 t else e21 t

theorem two_shear_word_ne_rotation
    (orientation₁ orientation₂ swap₀ swap₁ swap₂ : Bool)
    (a b : ℂ) :
    mul (mul (mul (mul (maybeSwap swap₀) (shear orientation₁ a))
      (maybeSwap swap₁)) (shear orientation₂ b))
      (maybeSwap swap₂) ≠ rotation := by
  cases orientation₁ <;> cases orientation₂ <;>
    cases swap₀ <;> cases swap₁ <;> cases swap₂ <;>
    simp [maybeSwap, shear, e21, e12, swap, one, mul, rotation]
  all_goals
    intro h
    norm_num at * <;> simp_all <;> norm_num

end TwoShearRotationNoGo
end ExactFourier
end OAI
