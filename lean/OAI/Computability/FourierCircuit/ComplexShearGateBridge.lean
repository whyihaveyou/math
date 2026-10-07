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
  k.castSucc.castSucc.castSucc

private def firstGateIndex {n : ℕ} : Fin (n + 1 + 1) :=
  Fin.last (n + 1)

private def secondGateIndex {n : ℕ} : Fin (n + 1 + 2) :=
  Fin.last (n + 1 + 1)

/-- Two scalar gates realize one arbitrary complex transvection.

The first gate computes `s.c * x s.j`; the second computes
`x s.i + s.c * x s.j`.  The remaining outputs are direct reads of the input
coordinates, which are free in `LinearDAG`.
-/
noncomputable def twoGateShear {n : ℕ} (s : Shear (Fin n)) : LinearDAG n n where
  size := 2
  program :=
    (Program.nil.step (Gate.scale s.c s.j.castSucc)).step
      (Gate.add s.i.castSucc.castSucc firstGateIndex)
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
      firstGateIndex, secondGateIndex, inputIndex, Gate.eval,
      Fin.snoc_last, Fin.snoc_castSucc]
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


/-- Direct input wires for the one-gate unit-coefficient realization. -/
private def unitInputIndex {n : ℕ} (k : Fin n) : Fin (n + 1 + 1) :=
  k.castSucc.castSucc

private def unitGateIndex {n : ℕ} : Fin (n + 1 + 1) :=
  Fin.last (n + 1)

/-- When the shear coefficient is `1`, a single `Gate.add` realizes the
transvection.  This is the exact unit-coefficient case relevant to a possible
primitive one-direction route; arbitrary coefficients still use the two-gate
bridge above. -/
noncomputable def oneGateUnitShear {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) : LinearDAG n n where
  size := 1
  program := Program.nil.step (Gate.add s.i.castSucc s.j.castSucc)
  outputs := fun k => if k = s.i then unitGateIndex else unitInputIndex k

@[simp] theorem oneGateUnitShear_size {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) :
    (oneGateUnitShear s hc).size = 1 := rfl

/-- Exact semantics of the unit-coefficient one-gate realization. -/
theorem oneGateUnitShear_eval {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) (x : Fin n → ℂ) :
    (oneGateUnitShear s hc).eval x = s.act x := by
  funext k
  by_cases hk : k = s.i
  · subst k
    simp [oneGateUnitShear, LinearDAG.eval, Program.eval, Shear.act,
      unitGateIndex, unitInputIndex, hc, Gate.eval]
  · simp [oneGateUnitShear, LinearDAG.eval, Program.eval, Shear.act,
      unitGateIndex, unitInputIndex, hc, Gate.eval, hk]

/-- Matrix form of the unit-coefficient realization. -/
theorem oneGateUnitShear_matrix {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) :
    ∀ x, (oneGateUnitShear s hc).eval x = s.toMatrix.mulVec x := by
  intro x
  rw [oneGateUnitShear_eval, Shear.act_eq_mulVec]

/-- A one-gate witness for a unit-coefficient shear. -/
structure UnitShearWitness (n : ℕ) (s : Shear (Fin n)) where
  coefficient_one : s.c = (1 : ℂ)
  circuit : LinearDAG n n
  size_eq_one : circuit.size = 1
  computes : ∀ x, circuit.eval x = s.toMatrix.mulVec x

noncomputable def unitShearWitness {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) : UnitShearWitness n s where
  coefficient_one := hc
  circuit := oneGateUnitShear s hc
  size_eq_one := oneGateUnitShear_size s hc
  computes := oneGateUnitShear_matrix s hc

@[simp] theorem unitShearWitness_size {n : ℕ} (s : Shear (Fin n))
    (hc : s.c = (1 : ℂ)) :
    (unitShearWitness s hc).circuit.size = 1 := rfl

end ComplexShearGateBridge
end ExactFourier
end OAI
