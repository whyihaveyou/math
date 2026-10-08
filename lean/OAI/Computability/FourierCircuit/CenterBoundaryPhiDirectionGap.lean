import OAI.Computability.FourierCircuit.CenterBoundarySelectiveFrameEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# The missing `Phi` direction-step interface at the selective centre boundary

The paper's frame lemma assigns a directional-kernel count only after its two
endpoint labels are nested.  The local selective transvection proved in
`CenterBoundarySelectiveFrameEquiv` is stronger in a different direction: it
is an isometric equivalence between the *whole* selected source and target
labels.  Those labels are nevertheless incomparable.  Consequently the
restricted `W` transport cannot by itself be fed to the paper's nested-label
`Phi_V Phi_U⁻¹` factorization.

This file makes that API boundary explicit.  `NestedResidualRankWitness` is
the binary linear-algebra part that a future `Phi` proof must provide: an
orientation of the endpoint labels, a residual decomposition, and a rank
(`rho`) for the directional kernels.  No complex matrix or gate schedule is
postulated here.  The selective endpoint theorem below proves that no such
witness can use the two currently proposed endpoint labels.  Passing through
their join costs exactly one residual dimension in each direction, as already
proved by the local boundary audit.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryPhiDirectionGap

open CenterBoundaryCommonFrameEdge
open CenterBoundarySelectiveFrameEquiv
open CenterBoundarySelectiveTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

/-!
The binary rank/decomposition data needed before applying the paper's
directional-kernel lemma.  The field `directionCount` is intentionally just
the residual rank; the complex `Phi` factorization that turns this rank into
actual gates is a separate future premise.
-/
structure NestedResidualRankWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (source target : Submodule F (Address ι h)) where
  small : Submodule F (Address ι h)
  large : Submodule F (Address ι h)
  endpoint_orientation :
    (small = source ∧ large = target) ∨
      (small = target ∧ large = source)
  nested : small ≤ large
  residual : Submodule F (Address ι h)
  residual_le_large : residual ≤ large
  residual_orthogonal_small :
    residual ≤ small.orthogonalBilin
      (BinaryTransvection.bilinearDot : _)
  decomposition : large = small ⊔ residual
  disjoint : Disjoint small residual
  directionCount : ℕ
  directionCount_eq :
    directionCount = Module.finrank F residual

def HasNestedResidualRankWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (source target : Submodule F (Address ι h)) : Prop :=
  Nonempty (NestedResidualRankWitness source target)

/- The rank conclusion is the exact arithmetic output expected by the
   nested-label `Phi` lemma once its decomposition has been supplied. -/
theorem NestedResidualRankWitness.directionCount_eq_finrank_difference
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    {source target : Submodule F (Address ι h)}
    (W : NestedResidualRankWitness source target) :
    W.directionCount =
      Module.finrank F W.large - Module.finrank F W.small := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W.small W.residual
  have hdisj : W.small ⊓ W.residual =
      (⊥ : Submodule F (Address ι h)) := W.disjoint.eq_bot
  have hsup : Module.finrank F
      (W.small ⊔ W.residual : Submodule F (Address ι h)) =
      Module.finrank F W.small + Module.finrank F W.residual := by
    rw [← hdim, hdisj, finrank_bot, add_zero]
  have hlarge : Module.finrank F W.large =
      Module.finrank F W.small + Module.finrank F W.residual := by
    rw [W.decomposition]
    exact hsup
  rw [W.directionCount_eq]
  omega

/-!
The exact prerequisite is nestedness, independent of whether the selected
linear equivalence is an isometry.  This helper lets callers state the
paper's endpoint requirement without inventing a complex embedding of the
binary labels.
-/
def HasNestedPhiEndpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (source target : Submodule F (Address ι h)) : Prop :=
  source ≤ target ∨ target ≤ source

theorem selective_endpoints_not_nestedPhi
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) (hw : t w = 0) :
    ¬ HasNestedPhiEndpoints (selectiveSource p x t)
      (selectiveTarget p x t w) := by
  exact selective_endpoints_not_nested p x t w hp ht hxt hxw hw

/- A `NestedResidualRankWitness` necessarily supplies the missing endpoint
   nesting.  Therefore it cannot exist for the selective endpoints. -/
theorem no_selective_nestedResidualRankWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) (hw : t w = 0) :
    ¬ HasNestedResidualRankWitness
        (selectiveSource p x t) (selectiveTarget p x t w) := by
  rintro ⟨W⟩
  rcases W.endpoint_orientation with ⟨hsmall, hlarge⟩ | ⟨hsmall, hlarge⟩
  · apply selective_endpoints_not_nested p x t w hp ht hxt hxw hw
    left
    simpa only [hsmall, hlarge] using W.nested
  · apply selective_endpoints_not_nested p x t w hp ht hxt hxw hw
    right
    simpa only [hsmall, hlarge] using W.nested

/-!
If the route is repaired through the common join, the two orientations have
an exact one-dimensional residual increment each.  This is the strongest
local direction-count statement available without a legal `Phi` factorization
for the selective map.
-/
theorem selective_join_direction_count_exact_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) (hw : t w = 0) :
    joinResidualCost (selectiveSource p x t)
          (selectiveTarget p x t w) = 1 ∧
      joinResidualCost (selectiveTarget p x t w)
          (selectiveSource p x t) = 1 ∧
      joinResidualCost (selectiveSource p x t) (selectiveTarget p x t w) +
          joinResidualCost (selectiveTarget p x t w)
            (selectiveSource p x t) = 2 := by
  have hforward := selective_join_cost_source_target_eq_one
    p x t w hp ht hxt hxw hw
  have hbackward := selective_join_cost_target_source_eq_one
    p x t w hp ht hxt hxw hw
  exact ⟨hforward, hbackward, by omega⟩

/- The local `W` map does provide exact restricted isometric transport and
   equal endpoint rank.  Keeping this theorem adjacent to the no-go prevents
   a future caller from confusing that fact with a nested `Phi` certificate. -/
theorem selective_W_transport_isometry_and_rank
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (p : ι → F) (x t : Active h) (w : Fin h)
    (hp : dotProduct p p = (1 : F))
    (ht : dotProduct t t = (1 : F))
    (hxt : dotProduct x t = 0) (hxw : x w = 0) (hw : t w = 0) :
    (∀ z z' : selectiveSource p x t,
      dotProduct
        (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw z : Address ι h)
        (WSelectiveRestrictedEquiv p x t w hp ht hxt hw hxw z' : Address ι h) =
        dotProduct (z : Address ι h) (z' : Address ι h)) ∧
      Module.finrank F (selectiveSource p x t) =
        Module.finrank F (selectiveTarget p x t w) := by
  constructor
  · intro z z'
    exact WSelectiveRestrictedEquiv_dot p x t w hp ht hxt hw hxw z z'
  · exact selective_endpoint_finrank_eq p x t w hp ht hxt hw hxw

end CenterBoundaryPhiDirectionGap
end ExactFourier
end OAI
