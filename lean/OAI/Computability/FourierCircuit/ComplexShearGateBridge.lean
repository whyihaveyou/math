import OAI.Computability.FourierCircuit.LinearDAG
import OAI.Computability.FourierCircuit.Shears

/-!
# Scalar-gate semantics for an elementary complex shear

`Shear` is the matrix-level primitive used by the replay and frame-cost
arguments.  The actual circuit model charges scalar `Gate`s.  This file gives
the smallest exact bridge currently available: one arbitrary complex
transvection is realized by two scalar gates (scale the source, then add the
scaled value to the destination), while all other inputs are exposed by
read-only outputs.

The result is intentionally one-way.  It supplies a concrete scalar-gate
realizer for a matrix-level shear, but it does not identify a `ZMod 2` frame
label with a complex coordinate vector, nor does it provide a global schedule.
Consequently, a directional unit in a conditional frame ledger cannot be
silently read as a scalar-gate cost without an additional compatibility and
accounting theorem.
-/

namespace OAI
namespace ExactFourier
namespace ComplexShearGateBridge

private def inputIndex {n : ℕ} (k : Fin n) : Fin (n + 1 + 2) :=
  ⟨k.val, by omega⟩

private def firstGateIndex {n : ℕ} : Fin (n + 1 + 1) :=
  ⟨n + 1, by omega⟩

private def secondGateIndex {n : ℕ} : Fin (n + 1 + 2) :=
  ⟨n + 2, by omega⟩

/-- Two scalar gates realize one arbitrary complex transvection.

The first gate computes `s.c * x s.j`; the second computes
`x s.i + s.c * x s.j`.  The remaining outputs are direct reads of the input
coordinates, which are free in `LinearDAG`.
-/
noncomputable def twoGateShear {n : ℕ} (s : Shear (Fin n)) : LinearDAG n n where
  size := 2
  program :=
    (Program.nil.step (Gate.scale s.c ⟨s.j.val, by omega⟩)).step
      (Gate.add ⟨s.i.val, by omega⟩ firstGateIndex)
  outputs := fun k => if k = s.i then secondGateIndex else inputIndex k

@[simp] theorem twoGateShear_size {n : ℕ} (s : Shear (Fin n)) :
    (twoGateShear s).size = 2 := rfl

/-- Exact scalar semantics of the two-gate realization. -/
theorem twoGateShear_eval {n : ℕ} (s : Shear (Fin n)) (x : Fin n → ℂ) :
    (twoGateShear s).eval x = s.act x := by
  funext k
  by_cases hk : k = s.i
  · subst k
    simp [twoGateShear, LinearDAG.eval, Program.eval, Shear.act,
      firstGateIndex, secondGateIndex, inputIndex]
  · simp [twoGateShear, LinearDAG.eval, Program.eval, Shear.act,
      firstGateIndex, secondGateIndex, inputIndex, hk]

/-- Matrix form of the same bridge. -/
theorem twoGateShear_matrix {n : ℕ} (s : Shear (Fin n)) :
    ∀ x, (twoGateShear s).eval x = s.toMatrix.mulVec x := by
  intro x
  rw [twoGateShear_eval, Shear.act_eq_mulVec]

/-- A finite-gate witness exposing the exact cost bound needed by a later
frame-compatible schedule.  The frame relation itself is deliberately left as
an explicit premise in downstream developments. -/
structure ScalarShearWitness (n : ℕ) (s : Shear (Fin n)) where
  circuit : LinearDAG n n
  size_le_two : circuit.size ≤ 2
  computes : ∀ x, circuit.eval x = s.toMatrix.mulVec x

/-- The bridge packages a concrete witness without asserting any frame
interpretation. -/
noncomputable def scalarShearWitness {n : ℕ} (s : Shear (Fin n)) :
    ScalarShearWitness n s where
  circuit := twoGateShear s
  size_le_two := by simp
  computes := twoGateShear_matrix s

@[simp] theorem scalarShearWitness_size {n : ℕ} (s : Shear (Fin n)) :
    (scalarShearWitness s).circuit.size = 2 := rfl

end ComplexShearGateBridge
end ExactFourier
end OAI
