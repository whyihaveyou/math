import OAI.Computability.FourierCircuit.SideRowGeneralArbitrary
import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic

/-!
# Reusing the side residual under an active-label swap

For a fixed prefix `p`, the side transition `x -> y` inserts the orthogonal
complement of the unordered pair `{x,y}`.  The reverse transition `y -> x`
therefore inserts exactly the same residual submodule.  This gives a genuine
frame-compatible reuse certificate when the same prefix frame is retained
across an alternating pair of active labels.

The statement is deliberately conditional on that fixed-prefix boundary.  It
does not identify the three different prefix types in the paper's global
schedule.  The final arithmetic ledger charges one reused direction per
h=24 invocation, so it accounts for the role-width effect of this local reuse
rather than treating it as a free exponent improvement.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SharedSideResidualAudit

open SideRowGeneralArbitrary

abbrev F := ZMod 2
abbrev D (h : ℕ) := Fin h → F
abbrev E (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}

/- The active pair-complement frame carried by a side residual. -/
def sharedFrame (p : ι → F) (x y : D h) : Submodule F (E ι h) :=
  residual p x y

/- Swapping the active labels leaves the pair-complement frame unchanged. -/
theorem pairPerp_swap (x y : D h) : pairPerp x y = pairPerp y x := by
  ext z
  rw [mem_pairPerp_iff, mem_pairPerp_iff]
  constructor <;> intro hz
  · exact ⟨hz.2, hz.1⟩
  · exact ⟨hz.2, hz.1⟩

/- The actual inserted residual is invariant under the active-label swap. -/
theorem residual_swap (p : ι → F) (x y : D h) :
    residual p x y = residual p y x := by
  change LinearMap.range ((insertP p).comp (pairPerp x y).subtype) =
    LinearMap.range ((insertP p).comp (pairPerp y x).subtype)
  rw [pairPerp_swap x y]

@[simp] theorem sharedFrame_swap (p : ι → F) (x y : D h) :
    sharedFrame p x y = sharedFrame p y x :=
  residual_swap p x y

/- The forward side row decomposes through the reusable pair frame. -/
theorem forward_row_reuse (p : ι → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = 0) :
    L5 p y = L2 p x ⊔ sharedFrame p x y := by
  exact side_row_decomp p x y hp hx hxy

/- The reverse side row uses the same reusable pair frame. -/
theorem reverse_row_reuse (p : ι → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hyx : dotProduct y x = 0) :
    L5 p x = L2 p y ⊔ sharedFrame p y x := by
  exact side_row_decomp p y x hp hy hyx

/- Both directions are certified against one and the same frame. -/
theorem alternating_rows_share_frame (p : ι → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = 0) :
    L5 p y = L2 p x ⊔ sharedFrame p x y ∧
      L5 p x = L2 p y ⊔ sharedFrame p x y := by
  have hforward := forward_row_reuse p x y hp hx hxy
  have hreverse := reverse_row_reuse p x y hp hy (by simpa [dotProduct_comm] using hxy)
  exact ⟨hforward, hreverse.trans (by rw [sharedFrame_swap])⟩

/-! ## Exact h = 24 direction and role-width ledger -/

namespace H24

abbrev h24 : ℕ := CenterCompression.H24.h
abbrev invocationCount : ℕ := CenterCompression.H24.I0
abbrev oldSideDirections : ℕ := 3 * (h24 - 2)
abbrev reusedSideDirections : ℕ := h24 - 2
abbrev sideDirectionReduction : ℕ := oldSideDirections - reusedSideDirections
abbrev width : ℕ := CenterCompression.H24.Wcompressed
abbrev widthAfterReuse : ℕ := width - invocationCount * sideDirectionReduction
abbrev two44 : ℕ := 2 ^ 44
abbrev two45 : ℕ := 2 ^ 45

@[simp] theorem h24_eq : h24 = 24 := by rfl
@[simp] theorem invocationCount_eq : invocationCount = 12289728 := by
  exact CenterCompression.H24.I0_eq

/- Three independent stage insertions charge 66 active directions. -/
theorem oldSideDirections_eq : oldSideDirections = 66 := by
  norm_num [oldSideDirections, h24]

/- Reusing the same pair frame across the alternating swap charges 22. -/
theorem reusedSideDirections_eq : reusedSideDirections = 22 := by
  norm_num [reusedSideDirections, h24]

/- The exact local reduction is 44 directional units. -/
theorem sideDirectionReduction_eq : sideDirectionReduction = 44 := by
  norm_num [sideDirectionReduction, oldSideDirections, reusedSideDirections, h24]

/- Under one-unit-per-direction-per-invocation charging, the role reduction is exact. -/
theorem roleReduction_eq : invocationCount * sideDirectionReduction = 540748032 := by
  rw [invocationCount_eq, sideDirectionReduction_eq]

/- The resulting width remains above 2^44, so binary padding is still 2^45. -/
theorem widthAfterReuse_eq : widthAfterReuse = 34666389539584 := by
  norm_num [widthAfterReuse, width, invocationCount, sideDirectionReduction,
    CenterCompression.H24.Wcompressed, CenterCompression.H24.I0,
    oldSideDirections, reusedSideDirections, h24, CenterCompression.H24.v,
    CenterCompression.H24.dNbr, CenterCompression.H24.N0, CenterCompression.H24.h,
    Nat.choose]

theorem widthAfterReuse_bounds : two44 < widthAfterReuse ∧ widthAfterReuse ≤ two45 := by
  norm_num [two44, two45, widthAfterReuse_eq]

/- This local reuse is a verified frame saving, but not yet a 10^-9 exponent result. -/
theorem reuse_does_not_cross_binary_boundary : two44 < widthAfterReuse :=
  widthAfterReuse_bounds.1

end H24
end SharedSideResidualAudit
end ExactFourier
end OAI
