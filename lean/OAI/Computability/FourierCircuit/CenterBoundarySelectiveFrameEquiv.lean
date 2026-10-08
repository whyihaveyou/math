import OAI.Computability.FourierCircuit.CenterBoundaryCommonFrameEdge
import Mathlib.Tactic

/-!
# Exact frame-label transport for the selective centre edge

`CenterBoundaryCommonFrameEdge` proves that the selective transvection maps
the source label `L₂ + 𝔽₂ d` into the target label `L₂ + 𝔽₂ e`, and that the
reverse inclusion holds after applying the involution.  This file packages
that local fact as an equality of submodules.  The equality is the precise
frame-label statement needed before a directional cost can be assigned: the
whole selected endpoint, rather than only its distinguished line, is
transported.

The result remains local.  It does not identify the map with a legal complex
gate, prove a common-frame action on the untouched wires, or provide a global
schedule.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundarySelectiveFrameEquiv

open CenterBoundaryCommonFrameEdge
open CenterBoundarySelectiveTransvection
open CenterRowGeneral

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

/-- The selective transvection transports the complete selected source label
    onto the complete selected target label. -/
theorem W_map_selectiveSource_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0) :
    Submodule.map (W p t w) (selectiveSource p x t) =
      selectiveTarget p x t w := by
  apply le_antisymm
  · intro z hz
    rcases Submodule.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact W_maps_selectiveSource p x t w hp ht hxt hw hxw hy
  · intro z hz
    refine Submodule.mem_map.mpr ⟨W p t w z, ?_, ?_⟩
    · exact W_maps_selectiveTarget p x t w hp ht hxt hw hxw hz
    · exact W_involutive p t w hp ht hw z

/-- The reverse image of the selected target label is exactly the selected
    source label.  This is the same frame statement in comap form. -/
theorem W_comap_selectiveTarget_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0) :
    (selectiveTarget p x t w).comap (W p t w) =
      selectiveSource p x t := by
  apply le_antisymm
  · intro z hz
    have hz' := W_maps_selectiveTarget p x t w hp ht hxt hw hxw
      (z := W p t w z) hz
    rw [W_involutive p t w hp ht hw z] at hz'
    exact hz'
  · intro z hz
    exact W_maps_selectiveSource p x t w hp ht hxt hw hxw hz

/-- The selected endpoint labels have equal dimension because the transvection
    is an isomorphism between them.  This is an exact label-rank identity, not
    an assumed one-direction cost. -/
noncomputable def WSelectiveRestrictedEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0) :
    selectiveSource p x t ≃ₗ[F] selectiveTarget p x t w := by
  let f : selectiveSource p x t →ₗ[F] selectiveTarget p x t w :=
    (W p t w).comp (selectiveSource p x t).subtype |>.codRestrict
      (selectiveTarget p x t w)
      (fun z => W_maps_selectiveSource p x t w hp ht hxt hw hxw z.property)
  have hinj : Function.Injective f := by
    intro z z' hzz'
    apply Subtype.ext
    have hval : W p t w (z : Address ι h) = W p t w (z' : Address ι h) := by
      exact congrArg (fun q : selectiveTarget p x t w => (q : Address ι h)) hzz'
    exact (WEquiv p t w hp ht hw).injective (by simpa only [WEquiv_apply] using hval)
  have hsurj : Function.Surjective f := by
    intro z
    let y : selectiveSource p x t :=
      ⟨W p t w (z : Address ι h),
        W_maps_selectiveTarget p x t w hp ht hxt hw hxw z.property⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact W_involutive p t w hp ht hw z
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

@[simp] theorem WSelectiveRestrictedEquiv_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (z : selectiveSource p x t) :
    (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw z :
      Address ι h) = W p t w (z : Address ι h) := by
  rfl

theorem WSelectiveRestrictedEquiv_dot
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (z z' : selectiveSource p x t) :
    dotProduct
        (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw z : Address ι h)
        (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw z' : Address ι h) =
      dotProduct (z : Address ι h) (z' : Address ι h) := by
  rw [WSelectiveRestrictedEquiv_apply, WSelectiveRestrictedEquiv_apply]
  exact W_isometry p t w hp ht hw (z : Address ι h) (z' : Address ι h)

theorem selective_endpoint_finrank_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0) :
    Module.finrank F (selectiveSource p x t) =
      Module.finrank F (selectiveTarget p x t w) := by
  exact (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw).finrank_eq

end CenterBoundarySelectiveFrameEquiv
end ExactFourier
end OAI
