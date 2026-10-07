import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace AllPairMomentIdentity

/-!
# Exact all-pair scalar identity (the `h = 6` audit instance)

For a fixed target triple `S`, write `a_F = ∑_{T ⊇ F} x_T` for the moment
attached to a pair `F`.  The three pair classes (two points in `S`, one
point in `S`, and no point in `S`) recover the diagonal-free side correction.
This file gives a completely finite, exact rational verification for `h = 6`.
It is intentionally independent of the frame and circuit-cost arguments.
-/

abbrev Point := Fin 6
abbrev Source := Fin 20
abbrev Pair := Fin 15

/-- The twenty 3-subsets of `Fin 6`, in lexicographic order. -/
def sourceLabel : Source → Finset Point
  | 0  => {0, 1, 2}
  | 1  => {0, 1, 3}
  | 2  => {0, 1, 4}
  | 3  => {0, 1, 5}
  | 4  => {0, 2, 3}
  | 5  => {0, 2, 4}
  | 6  => {0, 2, 5}
  | 7  => {0, 3, 4}
  | 8  => {0, 3, 5}
  | 9  => {0, 4, 5}
  | 10 => {1, 2, 3}
  | 11 => {1, 2, 4}
  | 12 => {1, 2, 5}
  | 13 => {1, 3, 4}
  | 14 => {1, 3, 5}
  | 15 => {1, 4, 5}
  | 16 => {2, 3, 4}
  | 17 => {2, 3, 5}
  | 18 => {2, 4, 5}
  | _  => {3, 4, 5}

/-- The fifteen 2-subsets of `Fin 6`, in lexicographic order. -/
def pairLabel : Pair → Finset Point
  | 0  => {0, 1}
  | 1  => {0, 2}
  | 2  => {0, 3}
  | 3  => {0, 4}
  | 4  => {0, 5}
  | 5  => {1, 2}
  | 6  => {1, 3}
  | 7  => {1, 4}
  | 8  => {1, 5}
  | 9  => {2, 3}
  | 10 => {2, 4}
  | 11 => {2, 5}
  | 12 => {3, 4}
  | 13 => {3, 5}
  | 14 => {4, 5}

abbrev target : Finset Point := {0, 1, 2}

/-- The source-to-pair moment `a_F`. -/
def pairMoment (x : Source → ℚ) (F : Pair) : ℚ :=
  ∑ T : Source, if pairLabel F ⊆ sourceLabel T then x T else 0

/-- Sum of pair moments in one of the three classes relative to the target. -/
def pairClassMoment (x : Source → ℚ) (p : Pair → Prop) [DecidablePred p] : ℚ :=
  ∑ F : Pair, if p F then pairMoment x F else 0

def pairInside (F : Pair) : Prop := pairLabel F ⊆ target
def pairOne (F : Pair) : Prop := (pairLabel F ∩ target).card = 1
def pairZero (F : Pair) : Prop := (pairLabel F ∩ target).card = 0

/- The predicates above are computational on the finite `Finset` labels.  We
   register their concrete decidability rather than using `Classical`, so the
   `native_decide` checks below remain executable. -/
instance pairInside_decidable (F : Pair) : Decidable (pairInside F) := by
  unfold pairInside
  exact inferInstance

instance pairOne_decidable (F : Pair) : Decidable (pairOne F) := by
  unfold pairOne
  exact inferInstance

instance pairZero_decidable (F : Pair) : Decidable (pairZero F) := by
  unfold pairZero
  exact inferInstance

/-- The coefficient of a source triple in the diagonal-free side map. -/
def sideCoeff (T : Source) : ℚ :=
  ((1 : ℚ) - ((sourceLabel T ∩ target).card : ℚ)) / 2

def sideNoDiag (x : Source → ℚ) : ℚ := ∑ T : Source, sideCoeff T * x T

/-- All pair classes have their expected exact multiplicities for each source
triple.  This is the finite `h = 6` incidence count, checked by computation. -/
theorem pair_class_counts (T : Source) :
    (∑ F : Pair, if pairInside F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) =
        (((sourceLabel T ∩ target).card.choose 2 : ℕ) : ℚ) ∧
    (∑ F : Pair, if pairOne F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) =
        (((sourceLabel T ∩ target).card * (3 - (sourceLabel T ∩ target).card) : ℕ) : ℚ) ∧
    (∑ F : Pair, if pairZero F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) =
        (((3 - (sourceLabel T ∩ target).card).choose 2 : ℕ) : ℚ) := by
  fin_cases T <;> native_decide

/-- The all-pair formula has exactly the side coefficient at every source
triple.  The displayed weights are `-1/3`, `-1/12`, and `+1/6`. -/
theorem all_pair_coeff (T : Source) :
    -(1 : ℚ) / 3 *
        (∑ F : Pair, if pairInside F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) +
      -(1 : ℚ) / 12 *
        (∑ F : Pair, if pairOne F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) +
      (1 : ℚ) / 6 *
        (∑ F : Pair, if pairZero F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) =
      sideCoeff T := by
  fin_cases T <;> native_decide

/-- Swap the finite source/pair sums in one pair class. -/
theorem pairClassMoment_expand
    (x : Source → ℚ) (p : Pair → Prop) [DecidablePred p] :
    pairClassMoment x p =
      ∑ T : Source,
        (∑ F : Pair,
          if p F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) * x T := by
  classical
  unfold pairClassMoment pairMoment
  have hsplit (F : Pair) :
      (if p F then (∑ T : Source,
          if pairLabel F ⊆ sourceLabel T then x T else 0) else 0) =
        ∑ T : Source,
          if p F ∧ pairLabel F ⊆ sourceLabel T then x T else 0 := by
    by_cases hp : p F
    · simp [hp]
    · simp [hp]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hp : p F ∧ pairLabel F ⊆ sourceLabel T <;> simp [hp]

/-- Exact scalar identity for arbitrary source values on the twenty triples. -/
theorem all_pair_moment_identity (x : Source → ℚ) :
    -(1 : ℚ) / 3 * pairClassMoment x pairInside +
      -(1 : ℚ) / 12 * pairClassMoment x pairOne +
      (1 : ℚ) / 6 * pairClassMoment x pairZero =
      sideNoDiag x := by
  classical
  rw [pairClassMoment_expand x pairInside,
    pairClassMoment_expand x pairOne,
    pairClassMoment_expand x pairZero]
  unfold sideNoDiag
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    -(1 : ℚ) / 3 *
          ((∑ F : Pair,
            if pairInside F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) * x T) +
        -(1 : ℚ) / 12 *
          ((∑ F : Pair,
            if pairOne F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) * x T) +
        (1 : ℚ) / 6 *
          ((∑ F : Pair,
            if pairZero F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) * x T) =
        (-(1 : ℚ) / 3 *
            (∑ F : Pair,
              if pairInside F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) +
          -(1 : ℚ) / 12 *
            (∑ F : Pair,
              if pairOne F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0) +
          (1 : ℚ) / 6 *
            (∑ F : Pair,
              if pairZero F ∧ pairLabel F ⊆ sourceLabel T then (1 : ℚ) else 0)) * x T := by ring
    _ = sideCoeff T * x T := by rw [all_pair_coeff T]

end AllPairMomentIdentity
end ExactFourier
end OAI
