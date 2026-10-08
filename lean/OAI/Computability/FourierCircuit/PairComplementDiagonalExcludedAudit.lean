import OAI.Computability.FourierCircuit.PairTargetFrameLocal
import OAI.Computability.FourierCircuit.PairComplementAggregateBoundary
import OAI.Computability.FourierCircuit.PairComplementSideArithmetic
import Mathlib.Tactic

/-!
# Diagonal-excluded pair/complement frame audit

The pair bank is read at a target `S` after its diagonal source `T = S` has
been separated into the direct source bank.  For the `A_F` bank (`F ⊂ S`),
the remaining labels are the off-diagonal source span `sourceSpan F k`, where
`S = insert k F`; its exact binary rank is `h - 3`.  The target-indexed family
of these spans nevertheless joins back to the full pair span of rank `h - 2`,
and the common intersection is trivial.  Thus diagonal exclusion gives a
real local frame, but not a globally reusable one.

The aggregate-wise four-edge ledger is also audited at rank `h - 3`: its
integer charge is still `e*h`.  This prevents a false claim that deleting the
diagonal automatically lowers the existing boundary price.  The companion
finite script checks the `B_F` bank: after deleting its diagonal source its
rank remains `h - 2` at `h = 24`.

All statements here are label-space/rank facts and conditional arithmetic.
They do not construct a complex gate, a global schedule, or an all-length DFT.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementDiagonalExcludedAudit

open PairTargetFrameLocal
open PairComplementAggregateBoundary

abbrev F := ZMod 2

namespace H24

abbrev h : ℕ := 24

/- The target `S = insert k F` has one distinguished coordinate `k` outside
   its pair prefix.  Removing `S` leaves exactly the `sourceSpan F k` family. -/
theorem off_diagonal_A_rank
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2)
    (k : Fin 24) (hk : k ∉ Fset) :
    Module.finrank F (sourceSpan Fset k) = 21 := by
  simpa using sourceSpan_finrank Fset k hF hk

theorem off_diagonal_A_rank_formula
    {h : ℕ} (Fset : Finset (Fin h)) (hF : Fset.card = 2)
    (k : Fin h) (hk : k ∉ Fset) :
    Module.finrank F (sourceSpan Fset k) = h - 3 := by
  exact sourceSpan_finrank Fset k hF hk

/- Every target-excluded A span is contained in the pair span, and the join of
   all target choices recovers that pair span. -/
theorem target_excluded_A_join_eq_pairSpan
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    allTargetSourceSpan Fset = pairSpan Fset := by
  exact allTargetSourceSpan_eq_pairSpan Fset hF (by norm_num)

theorem target_excluded_A_join_rank
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2) :
    Module.finrank F (allTargetSourceSpan Fset) = 22 := by
  rw [target_excluded_A_join_eq_pairSpan Fset hF]
  exact pairSpan_finrank Fset hF

/- The local target spans have no nonzero vector in common.  This is the
   precise obstruction to treating diagonal exclusion as a free shared frame.
-/
theorem no_nonzero_common_A_vector
    (Fset : Finset (Fin 24)) (hF : Fset.card = 2)
    (x : Fin 24 → F)
    (hx : ∀ k : Fin 24, k ∉ Fset → x ∈ sourceSpan Fset k) :
    x = 0 := by
  exact common_sourceSpan_eq_bot Fset hF (by norm_num) x hx

/- The four-edge aggregate ledger remains e*h when the local support rank is
   h-3 (the deleted diagonal consumes the extra codimension at the next edge).
-/
theorem diagonal_excluded_blockCost_eq
    (e : ℕ) (he : 1 ≤ e) :
    blockCost e 24 (24 - 3) = e * 24 := by
  unfold blockCost edgeZero edgeZeroToTwo edgeTwoToFive edgeFiveToSeven
  omega

theorem diagonal_excluded_threeStageCost_eq :
    blockCost 1 24 (24 - 3) +
      blockCost 24 24 (24 - 3) +
      blockCost (24 * 24) 24 (24 - 3) = 14424 := by
  norm_num [blockCost, edgeZero, edgeZeroToTwo, edgeTwoToFive,
    edgeFiveToSeven]

end H24
end PairComplementDiagonalExcludedAudit
end ExactFourier
end OAI
