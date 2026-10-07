import OAI.Computability.FourierCircuit.CenterBoundarySelectiveTransvection
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-!
# Common-frame edge interface for the selective centre transvection

`CenterBoundarySelectiveTransvection` proves a local binary transvection
which fixes the old source row and sends the missing direct line to a legal
coordinate line.  The paper's frame construction has a stronger requirement:
an edge map must transport the *whole* endpoint label, because every vector on
the touched array uses one common frame.  This file makes that distinction an
explicit Lean interface.

The old target boundary is not preserved by the proposed transvection, so it
cannot be a self-edge of that common boundary.  We also package the weaker
restricted transport on `L2 + span(d) -> L2 + span(e)`.  The latter is a
selective-edge algebraic interface only; its directional cost is deliberately
an explicit parameter, with no claim that it is one legal paper gate.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryCommonFrameEdge

open CenterRowGeneral
open CenterBoundaryObstruction
open CenterBoundarySelectiveTransvection
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

/- A fixed-width binary map which is legal as a common-frame self-edge for a
label `L`.  The equivalence transports every vector in the endpoint label;
this is the part that a selective algebraic witness cannot omit. -/
structure CommonFrameSelfEdge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (L : Submodule F (Address ι h)) where
  map : Address ι h ≃ₗ[F] Address ι h
  isometry : ∀ z z',
    dotProduct (map z) (map z') = dotProduct z z'
  label_transport : ∀ z, map z ∈ L ↔ z ∈ L

/- The boundary-preservation condition extracted from a common-frame edge. -/
def CommonFramePreserves
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (L : Submodule F (Address ι h))
    (U : Address ι h ≃ₗ[F] Address ι h) : Prop :=
  ∀ z, U z ∈ L ↔ z ∈ L

@[simp] theorem CommonFrameSelfEdge.preserves
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    {L : Submodule F (Address ι h)} (E : CommonFrameSelfEdge L) :
    CommonFramePreserves L E.map := by
  exact E.label_transport

/- The involutive transvection has a linear-equivalence presentation. -/
noncomputable def WEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0) :
    Address ι h ≃ₗ[F] Address ι h := by
  let f : Address ι h →ₗ[F] Address ι h := W p t w
  have hinv : Function.Involutive f := by
    simpa [f] using W_involutive p t w hp ht hw
  have hbij : Function.Bijective f := by
    constructor
    · intro z z' hzz'
      calc
        z = f (f z) := (hinv z).symm
        _ = f (f z') := congrArg f hzz'
        _ = z' := hinv z'
    · intro z
      exact ⟨f z, hinv z⟩
  exact LinearEquiv.ofBijective f hbij

@[simp] theorem WEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (p : ι → F) (t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (hw : t w = 0)
    (z : Address ι h) :
    WEquiv p t w hp ht hw z = W p t w z := by
  rfl

/- The proposed transvection cannot be a common-frame self-edge of the old
`L5` boundary.  This is the exact no-go needed before assigning it a
one-direction price. -/
theorem W_not_commonFrameSelfEdge
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (t : Active h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F)) (w : Fin h) (hw : t w = 0) :
    ¬ CommonFramePreserves (L5 p t) (WEquiv p t w hp ht hw) := by
  intro hpres
  apply W_does_not_preserve_L5 p t w hp ht hw
  intro z hz
  have hiff := hpres z
  have hmem : WEquiv p t w hp ht hw z ∈ L5 p t := hiff.mpr hz
  simpa only [WEquiv_apply] using hmem

/- The smaller source and target spaces for a genuinely selective transport.
They contain the old source row and one distinguished direct line. -/
def selectiveSource
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x : Active h) (t : Active h) :
    Submodule F (Address ι h) := L2 p x ⊔ (F ∙ d p t)

def selectiveTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x : Active h) (t : Active h) (w : Fin h) :
    Submodule F (Address ι h) := L2 p x ⊔ (F ∙ e p w)

/- The selected target is still inside the old target boundary.  Thus the
source's distinguished direct line cannot be carried into it: this is the
precise failure of the paper's comparable-label premise for the old frame. -/
theorem selectiveTarget_le_L5
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) :
    selectiveTarget p x t w ≤ L5 p t := by
  apply sup_le
  · exact L2_le_L5 p x t hxt
  · intro z hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (e_mem_L5 p t w hp hw)

theorem selectiveSource_not_le_selectiveTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) :
    ¬ selectiveSource p x t ≤ selectiveTarget p x t w := by
  intro hnest
  have hdsource : d p t ∈ selectiveSource p x t := by
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self (d p t))
  have hdtgt : d p t ∈ selectiveTarget p x t w := hnest hdsource
  have hdl5 : d p t ∈ L5 p t := selectiveTarget_le_L5 p x t w hp hxt hw hdtgt
  exact d_not_mem_L5 p t hp ht hdl5

/- The selected target line is not already in the old source row (the
coordinate has a one at `w`, while `x` has a zero there). -/
theorem e_not_mem_L2
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxw : x w = 0) :
    e p w ∉ L2 p x := by
  intro he
  rw [Submodule.mem_comap] at he
  rcases Submodule.mem_span_singleton.mp he with ⟨a, ha⟩
  have heq : coordinate w = a • x := by
    rw [project_insertP p hp] at ha
    simpa only using ha.symm
  have hval := congrFun heq w
  simp [coordinate, hxw] at hval

/- The target endpoint is not contained in the source endpoint either.  This
   rules out both orientations of a direct nested-label edge. -/
theorem selectiveTarget_not_le_selectiveSource
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (hxw : x w = 0) (hw : t w = 0) :
    ¬ selectiveTarget p x t w ≤ selectiveSource p x t := by
  intro hnest
  have heT : e p w ∈ selectiveTarget p x t w := by
    exact Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self (e p w))
  have heS : e p w ∈ selectiveSource p x t := hnest heT
  change e p w ∈ L2 p x ⊔ (F ∙ d p t) at heS
  rcases Submodule.mem_sup.mp heS with ⟨z₀, hz₀, z₁, hz₁, hsum⟩
  rcases Submodule.mem_span_singleton.mp hz₁ with ⟨a, ha⟩
  have hzline : projectP p z₀ ∈ line x := hz₀
  rcases Submodule.mem_span_singleton.mp hzline with ⟨b, hb⟩
  have hproj := congrArg (projectP p) hsum
  rw [map_add, ← ha, map_smul, project_insertP p hp, project_insertP p hp] at hproj
  rw [← hb] at hproj
  have hval := congrFun hproj w
  simp [e, coordinate, d, hxw, hw] at hval

/- The paper's directional-kernel lemma applies only to nested endpoint
labels.  The two local endpoint spaces fail both possible orientations, so a
direct edge cannot be assigned a residual dimension at all. -/
theorem selective_endpoints_not_nested
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) (hw : t w = 0) :
    ¬ (selectiveSource p x t ≤ selectiveTarget p x t w ∨
      selectiveTarget p x t w ≤ selectiveSource p x t) := by
  intro h
  rcases h with h | h
  · exact selectiveSource_not_le_selectiveTarget p x t w hp ht hxt hw h
  · exact selectiveTarget_not_le_selectiveSource p x t w hp hxw hw h

/- The transvection maps the selected source subspace into the selected legal
target subspace. -/
theorem W_maps_selectiveSource
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    {z : Address ι h} (hz : z ∈ selectiveSource p x t) :
    W p t w z ∈ selectiveTarget p x t w := by
  change z ∈ L2 p x ⊔ (F ∙ d p t) at hz
  change W p t w z ∈ L2 p x ⊔ (F ∙ e p w)
  rcases Submodule.mem_sup.mp hz with ⟨z₀, hz₀, z₁, hz₁, hsum⟩
  rcases Submodule.mem_span_singleton.mp hz₁ with ⟨a, rfl⟩
  rw [← hsum, map_add, map_smul, W_fix_L2 p x t w hp hxt hxw z₀ hz₀,
    W_map_d_to_e p t w hp ht hw]
  exact Submodule.mem_sup.mpr ⟨z₀, hz₀, a • e p w,
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (e p w)), rfl⟩

/- The same transport in the reverse direction; it follows from the
involution and is needed to state an actual restricted equivalence. -/
theorem W_maps_selectiveTarget
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    {z : Address ι h} (hz : z ∈ selectiveTarget p x t w) :
    W p t w z ∈ selectiveSource p x t := by
  change z ∈ L2 p x ⊔ (F ∙ e p w) at hz
  change W p t w z ∈ L2 p x ⊔ (F ∙ d p t)
  rcases Submodule.mem_sup.mp hz with ⟨z₀, hz₀, z₁, hz₁, hsum⟩
  rcases Submodule.mem_span_singleton.mp hz₁ with ⟨a, rfl⟩
  have hde : W p t w (e p w) = d p t := by
    have hi := W_involutive p t w hp ht hw (d p t)
    rw [W_map_d_to_e p t w hp ht hw] at hi
    exact hi
  rw [← hsum, map_add, map_smul, W_fix_L2 p x t w hp hxt hxw z₀ hz₀, hde]
  exact Submodule.mem_sup.mpr ⟨z₀, hz₀, a • d p t,
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (d p t)), rfl⟩

/- Restricted frame transport, with the directional cost kept as an explicit
parameter.  This is weaker than a paper gate: it says nothing about how the
map acts on the rest of a touched array or how it is scheduled. -/
structure SelectiveEdge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (source target : Submodule F (Address ι h)) where
  map : Address ι h ≃ₗ[F] Address ι h
  isometry : ∀ z z',
    dotProduct (map z) (map z') = dotProduct z z'
  restricted_transport : ∀ z, map z ∈ target ↔ z ∈ source
  directionalCost : ℕ

noncomputable def WSelectiveEdge
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (c : ℕ) : SelectiveEdge (selectiveSource p x t) (selectiveTarget p x t w) where
  map := WEquiv p t w hp ht hw
  isometry := by
    intro z z'
    exact W_isometry p t w hp ht hw z z'
  restricted_transport := by
    intro z
    constructor
    · intro hz
      have hzW : W p t w z ∈ selectiveTarget p x t w := by
        simpa only [WEquiv_apply] using hz
      have hz' : W p t w (W p t w z) ∈ selectiveSource p x t :=
        W_maps_selectiveTarget p x t w hp ht hxt hw hxw
          (z := W p t w z) hzW
      have hi := W_involutive p t w hp ht hw z
      rw [hi] at hz'
      exact hz'
    · intro hz
      have hz' : W p t w z ∈ selectiveTarget p x t w :=
        W_maps_selectiveSource p x t w hp ht hxt hw hxw (z := z) hz
      simpa only [WEquiv_apply] using hz'
  directionalCost := c

@[simp] theorem WSelectiveEdge_cost
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0)
    (c : ℕ) :
    (WSelectiveEdge p x t w hp ht hxt hw hxw c).directionalCost = c := by
  rfl

/- Any claimed one-direction implementation is an extra premise, not a
consequence of the local transvection algebra. -/
theorem WSelectiveEdge_one_direction
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hw : t w = 0) (hxw : x w = 0) :
    (WSelectiveEdge p x t w hp ht hxt hw hxw 1).directionalCost = 1 := by
  rfl

end CenterBoundaryCommonFrameEdge
end ExactFourier
end OAI
