import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Conditional support bound for termwise frame-compatible projection factors

Pairwise even-intersection triple indicators have binary Gram matrix equal to
identity, so a family has at most h members.  Applied separately to h rank-one
terms, this bounds the union of their diagonal supports by h^2.  The network
premise that each term is individually frame-compatible is deliberately
outside this file: arbitrary cancellation between terms is not covered.
-/

namespace OAI.ExactFourier.TermwiseProjectionSupportBound

open scoped BigOperators

abbrev F := ZMod 2

theorem gram_one_linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (w : ι → Fin h → F)
    (hgram : ∀ i j, dotProduct (w i) (w j) = if i = j then 1 else 0) :
    LinearIndependent F w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hz := congrArg (fun z : Fin h → F => dotProduct z (w j)) hg
  rw [sum_dotProduct] at hz
  simp only [smul_dotProduct, hgram, dotProduct_zero] at hz
  simpa using hz

theorem gram_one_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (w : ι → Fin h → F)
    (hgram : ∀ i j, dotProduct (w i) (w j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ h := by
  have hc := (gram_one_linearIndependent w hgram).fintype_card_le_finrank
  simpa using hc

/-- A union of h finite supports of size at most h has at most h^2 elements. -/
theorem union_support_card_le {α : Type*} [DecidableEq α] (h : ℕ)
    (supports : Fin h → Finset α) (hsize : ∀ i, (supports i).card ≤ h) :
    (Finset.univ.biUnion supports).card ≤ h * h := by
  calc
    (Finset.univ.biUnion supports).card ≤ ∑ i : Fin h, (supports i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin h, h := Finset.sum_le_sum (fun i _ => hsize i)
    _ = h * h := by simp

end OAI.ExactFourier.TermwiseProjectionSupportBound
