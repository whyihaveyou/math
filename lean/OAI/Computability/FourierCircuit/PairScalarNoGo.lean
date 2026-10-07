import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace PairScalarNoGo

/-!
# A scalar obstruction to pair-only source recovery

The eight triples obtained by choosing one point from each of the three
pairs `{0,1}`, `{2,3}`, and `{4,5}` carry the alternating coefficients
`(-1)^(b₁+b₂+b₃)`.  Every pair moment (and the global sum) vanishes on this
nonzero source.  Thus pair moments plus the global moment cannot have a left
inverse, even as an arbitrary nonlinear map.  This is a scalar obstruction;
it is independent of the frame labels and of any cost accounting.  It does
not rule out a construction that keeps an additional direct source-to-target
channel for the diagonal term.
-/

abbrev Point := Fin 6
abbrev Source := Bool × Bool × Bool

/-- The point selected from the first, second, or third coordinate pair. -/
def firstPoint : Bool → Point := fun b => if b then 1 else 0
def secondPoint : Bool → Point := fun b => if b then 3 else 2
def thirdPoint : Bool → Point := fun b => if b then 5 else 4

/-- One of the eight triples in the `2×2×2` octahedral witness. -/
def sourceLabel : Source → Finset Point
  | (b₁, b₂, b₃) => {firstPoint b₁, secondPoint b₂, thirdPoint b₃}

/-- The alternating signed source supported on the eight labels. -/
def witness : Source → ℤ
  | (b₁, b₂, b₃) =>
      (if b₁ then -1 else 1) *
      (if b₂ then -1 else 1) *
      (if b₃ then -1 else 1)

/-- A pair-incidence moment.  Ordered pairs are used so no quotient by
unordered pairs is needed; allowing diagonal pairs only gives the proposed
compression more information. -/
def pairMoment (x : Source → ℤ) (i j : Point) : ℤ :=
  ∑ b : Source, if i ∈ sourceLabel b ∧ j ∈ sourceLabel b then x b else 0

def totalMoment (x : Source → ℤ) : ℤ := ∑ b : Source, x b

@[simp] theorem pairMoment_zero (i j : Point) :
    pairMoment (0 : Source → ℤ) i j = 0 := by
  simp [pairMoment]

@[simp] theorem totalMoment_zero : totalMoment (0 : Source → ℤ) = 0 := by
  simp [totalMoment]

abbrev Moment := (Point → Point → ℤ) × ℤ

def moments (x : Source → ℤ) : Moment :=
  (pairMoment x, totalMoment x)

/- The three pairs contained in the fixed target `{0,2,4}`.  They are
represented directly by the corresponding Boolean tests; this avoids any
quotient by unordered pairs. -/
def localPair01 (x : Source → ℤ) : ℤ :=
  ∑ b : Source, if b.1 = false ∧ b.2.1 = false then x b else 0

def localPair02 (x : Source → ℤ) : ℤ :=
  ∑ b : Source, if b.1 = false ∧ b.2.2 = false then x b else 0

def localPair12 (x : Source → ℤ) : ℤ :=
  ∑ b : Source, if b.2.1 = false ∧ b.2.2 = false then x b else 0

abbrev LocalMoment := (ℤ × ℤ × ℤ) × ℤ

def localMoments (x : Source → ℤ) : LocalMoment :=
  ((localPair01 x, localPair02 x, localPair12 x), x (false, false, false))

/- The disjoint triple `{1,3,5}` is the missing `|S ∩ T| = 0` term. -/
def disjointContribution (x : Source → ℤ) : ℤ := x (true, true, true)

def disjointWitness : Source → ℤ := fun b =>
  if b = (true, true, true) then 1 else 0

@[simp] theorem disjointWitness_localPair01 : localPair01 disjointWitness = 0 := by
  native_decide

@[simp] theorem disjointWitness_localPair02 : localPair02 disjointWitness = 0 := by
  native_decide

@[simp] theorem disjointWitness_localPair12 : localPair12 disjointWitness = 0 := by
  native_decide

@[simp] theorem disjointWitness_target :
    disjointWitness (false, false, false) = 0 := by
  native_decide

@[simp] theorem disjointWitness_contribution :
    disjointContribution disjointWitness = 1 := by
  native_decide

theorem localMoments_disjointWitness_eq_zero :
    localMoments disjointWitness = localMoments 0 := by
  apply Prod.ext
  · apply Prod.ext
    · change localPair01 disjointWitness = localPair01 0
      rw [disjointWitness_localPair01]
      simp [localPair01]
    · apply Prod.ext
      · change localPair02 disjointWitness = localPair02 0
        rw [disjointWitness_localPair02]
        simp [localPair02]
      · change localPair12 disjointWitness = localPair12 0
        rw [disjointWitness_localPair12]
        simp [localPair12]
  · change disjointWitness (false, false, false) = (0 : Source → ℤ) (false, false, false)
    rw [disjointWitness_target]
    rfl

/- Even after retaining the direct target source coordinate, the three local
pairs do not determine the disjoint contribution required by the side
correction. -/
theorem no_local_pair_disjoint_reconstruction :
    ¬ ∃ R : LocalMoment → ℤ,
      ∀ x, R (localMoments x) = disjointContribution x := by
  rintro ⟨R, hR⟩
  have hw := hR disjointWitness
  have hzero := hR 0
  rw [localMoments_disjointWitness_eq_zero] at hw
  have hsame : disjointContribution disjointWitness = disjointContribution 0 := by
    calc
      disjointContribution disjointWitness = R (localMoments 0) := hw.symm
      _ = disjointContribution 0 := hzero
  rw [disjointWitness_contribution] at hsame
  simp [disjointContribution] at hsame

/-- The witness is invisible to every ordered pair moment. -/
theorem witness_pairMoment_zero : ∀ i j : Point, pairMoment witness i j = 0 := by
  native_decide

/-- The witness is also invisible to the global moment. -/
theorem witness_totalMoment_zero : totalMoment witness = 0 := by
  native_decide

/-- The witness itself is nonzero. -/
theorem witness_nonzero : witness (false, false, false) = 1 := by
  native_decide

theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  have hz := congrFun h (false, false, false)
  rw [witness_nonzero] at hz
  exact one_ne_zero hz

/-- Pair moments and the global moment cannot distinguish the witness from
zero. -/
theorem moments_witness_eq_zero : moments witness = moments 0 := by
  apply Prod.ext
  · funext i j
    change pairMoment witness i j = pairMoment 0 i j
    rw [witness_pairMoment_zero, pairMoment_zero]
  · change totalMoment witness = totalMoment 0
    rw [witness_totalMoment_zero, totalMoment_zero]

/-- No arbitrary reconstruction from pair moments plus the global moment can
recover every source coordinate.  Any exact implementation that uses these
aggregates therefore needs an additional source-dependent channel. -/
theorem no_left_inverse :
    ¬ ∃ R : Moment → (Source → ℤ), ∀ x, R (moments x) = x := by
  rintro ⟨R, hR⟩
  have hw := hR witness
  have hzero := hR 0
  rw [moments_witness_eq_zero] at hw
  have heq : witness = 0 := by
    calc
      witness = R (moments 0) := hw.symm
      _ = 0 := hzero
  exact witness_ne_zero heq

end PairScalarNoGo
end ExactFourier
end OAI
