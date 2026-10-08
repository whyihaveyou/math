import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Generic residual-rank interface for a rank-limited centre map

For an arbitrary linear map `P : X →ₗ[K] X`, the identity decomposes as
`P + (1-P)`.  Hence the two ranges span the whole source and the residual
range has dimension at least `finrank X - finrank P.range`.  This is a pure
rank statement; no frame or gate-cost premise is assumed.
-/

namespace OAI
namespace ExactFourier
namespace RankComplementLowerBound

variable {K X : Type*} [Field K]
variable [AddCommGroup X] [Module K X]
variable [FiniteDimensional K X]

/-- The identity range is contained in the sum of the centre and residual ranges. -/
theorem top_le_range_sup_range_sub (P : X →ₗ[K] X) :
    (⊤ : Submodule K X) ≤ P.range ⊔ (1 - P).range := by
  intro x hx
  have hcentre : P x ∈ P.range := LinearMap.mem_range_self P x
  have hresidual : x - P x ∈ (1 - P).range := by
    refine ⟨x, ?_⟩
    simp
  have hsum : x = P x + (x - P x) := by abel
  rw [hsum]
  exact Submodule.add_mem_sup hcentre hresidual

/-- Centre rank plus residual rank covers the ambient dimension. -/
theorem finrank_add_finrank_sub_ge (P : X →ₗ[K] X) :
    Module.finrank K X ≤ Module.finrank K P.range +
      Module.finrank K (1 - P).range := by
  have htop : (⊤ : Submodule K X) ≤ P.range ⊔ (1 - P).range :=
    top_le_range_sup_range_sub P
  have hdim : Module.finrank K X ≤
      Module.finrank K (P.range ⊔ (1 - P).range : Submodule K X) := by
    simpa using Submodule.finrank_mono htop
  exact hdim.trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- A rank-`h` centre map leaves at least `v-h` residual dimensions. -/
theorem residual_finrank_ge_sub (P : X →ₗ[K] X) (h : ℕ)
    (hP : Module.finrank K P.range ≤ h) :
    Module.finrank K X - h ≤ Module.finrank K (1 - P).range := by
  have hsum := finrank_add_finrank_sub_ge P
  omega

end RankComplementLowerBound
end ExactFourier
end OAI
