import OAI.Computability.FourierCircuit.BinaryTransvection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Centre-row residuals with an arbitrary finite prefix

Let the prefix address space have arbitrary finite coordinate type `ι`, and
let the active factor have `h` coordinates.  For a prefix label `p` of binary
norm one, fibrewise contraction and insertion split the address space into
`p⊥ ⊗ F₂^h` and `span(p) ⊗ F₂^h`.  The residual has the explicit orthonormal
basis `p ⊗ e_j` and exactly `h` directions, independently of the prefix size.

Thus the same statement applies to prefix dimensions `1`, `h`, and `h²` in
the three centre transitions.  It is a linear-algebra certificate; the full
network schedule, frame operators, and recursive operation count are separate.
-/

open scoped BigOperators

namespace OAI.ExactFourier.CenterRowGeneral

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι] {h : ℕ}

/-- Contraction against the prefix unit vector. -/
def project (p : ι → F) : Address ι h →ₗ[F] Active h where
  toFun x := fun j => dotProduct p (fun i => x (i, j))
  map_add' x y := by
    ext j
    change dotProduct p ((fun i => x (i, j)) + (fun i => y (i, j))) = _
    rw [dotProduct_add]
    rfl
  map_smul' a x := by
    ext j
    change dotProduct p (a • (fun i => x (i, j))) = _
    rw [dotProduct_smul]
    rfl

/-- Insertion along the prefix line: `d ↦ p ⊗ d`. -/
def insert (p : ι → F) : Active h →ₗ[F] Address ι h where
  toFun d := fun z => p z.1 * d z.2
  map_add' x y := by
    ext z
    exact mul_add _ _ _
  map_smul' a x := by
    ext z
    simp [smul_eq_mul, mul_left_comm]

abbrev parent (p : ι → F) : Submodule F (Address ι h) :=
  LinearMap.ker (project p)

abbrev residual (p : ι → F) : Submodule F (Address ι h) :=
  LinearMap.range (insert p)

@[simp] theorem project_insert (p : ι → F)
    (hp : dotProduct p p = (1 : F)) (d : Active h) :
    project p (insert p d) = d := by
  ext j
  have hfun : (fun i => p i * d j) = (d j) • p := by
    ext i
    exact mul_comm _ _
  change dotProduct p (fun i => p i * d j) = d j
  rw [hfun, dotProduct_smul, hp]
  simp

theorem insert_injective (p : ι → F)
    (hp : dotProduct p p = (1 : F)) :
    Function.Injective (insert (h := h) p) := by
  intro d e heq
  have hc := congrArg (project p) heq
  simpa only [project_insert p hp] using hc

/-- The parent is exactly the fibrewise prefix orthogonal complement. -/
theorem mem_parent_iff (p : ι → F) (x : Address ι h) :
    x ∈ parent p ↔ ∀ j : Fin h,
      (fun i => x (i, j)) ∈
        (F ∙ p).orthogonalBilin (BinaryTransvection.bilinearDot : _) := by
  simp only [Submodule.orthogonalBilin_span_singleton, LinearMap.mem_ker]
  change project p x = 0 ↔ ∀ j, dotProduct p (fun i => x (i, j)) = 0
  exact funext_iff

/-- Contraction is the adjoint of tensor insertion for the binary dot product. -/
theorem insert_dot (p : ι → F) (d : Active h) (x : Address ι h) :
    dotProduct (insert p d) x = dotProduct d (project p x) := by
  change (∑ z : ι × Fin h, p z.1 * d z.2 * x z) =
    ∑ j : Fin h, d j * ∑ i : ι, p i * x (i, j)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The residual and parent are orthogonal, with no dimension assumption on
    the prefix.  This equality itself does not require `p` to be unit. -/
theorem parent_eq_residual_orthogonal (p : ι → F) :
    parent (h := h) p =
      (residual p).orthogonalBilin (BinaryTransvection.bilinearDot : _) := by
  ext x
  constructor
  · intro hx
    apply Submodule.mem_orthogonalBilin.mpr
    rintro y ⟨d, rfl⟩
    change dotProduct (insert p d) x = 0
    rw [insert_dot, LinearMap.mem_ker.mp hx]
    simp
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext j
    have hj := Submodule.mem_orthogonalBilin.mp hx
      (insert p (BinaryTransvection.coordinate j))
      (LinearMap.mem_range_self (insert p) (BinaryTransvection.coordinate j))
    change dotProduct (insert p (BinaryTransvection.coordinate j)) x = 0 at hj
    rw [insert_dot, BinaryTransvection.coordinate_dot] at hj
    exact hj

private def projectionToResidual (p : ι → F) :
    Address ι h →ₗ[F] residual (h := h) p where
  toFun x := ⟨insert p (project p x), LinearMap.mem_range_self _ _⟩
  map_add' x y := by
    apply Subtype.ext
    change insert p (project p (x + y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a x := by
    apply Subtype.ext
    change insert p (project p (a • x)) = _
    rw [map_smul, map_smul]
    rfl

private theorem projectionToResidual_fix (p : ι → F)
    (hp : dotProduct p p = (1 : F)) (x : residual (h := h) p) :
    projectionToResidual p x = x := by
  apply Subtype.ext
  rcases x with ⟨x, ⟨d, rfl⟩⟩
  change insert p (project p (insert p d)) = insert p d
  rw [project_insert p hp]

/-- Full prefix-active space is the direct sum of parent and residual. -/
theorem row_isCompl (p : ι → F) (hp : dotProduct p p = (1 : F)) :
    IsCompl (residual (h := h) p) (parent (h := h) p) := by
  have hk : LinearMap.ker (projectionToResidual (h := h) p) = parent (h := h) p := by
    ext x
    constructor
    · intro hx
      have hz : insert p (project p x) = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have hz' := congrArg (project p) hz
      change project p x = 0
      simpa only [project_insert p hp, map_zero] using hz'
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change insert p (project p x) = 0
      rw [LinearMap.mem_ker.mp hx, map_zero]
  rw [← hk]
  exact LinearMap.isCompl_of_proj (projectionToResidual_fix p hp)

theorem residual_finrank (p : ι → F) (hp : dotProduct p p = (1 : F)) :
    Module.finrank F (residual (h := h) p) = h := by
  rw [LinearMap.finrank_range_of_inj (insert_injective p hp)]
  simp [Active]

/-- Tensor insertion preserves the active-factor dot product. -/
theorem insert_dot_insert (p : ι → F) (hp : dotProduct p p = (1 : F))
    (d e : Active h) :
    dotProduct (insert p d) (insert p e) = dotProduct d e := by
  rw [insert_dot, project_insert p hp]

/-- A basis of the residual, explicitly obtained by inserting the active
    coordinate vectors along `p`. -/
noncomputable def residualBasis (p : ι → F)
    (hp : dotProduct p p = (1 : F)) : Module.Basis (Fin h) F (residual (h := h) p) :=
  (Pi.basisFun F (Fin h)).map
    (LinearEquiv.ofInjective (insert p) (insert_injective p hp))

@[simp] theorem residualBasis_coe (p : ι → F)
    (hp : dotProduct p p = (1 : F)) (j : Fin h) :
    (residualBasis p hp j : Address ι h) =
      insert p (BinaryTransvection.coordinate j) := by
  simp [residualBasis, Module.Basis.map_apply, LinearEquiv.ofInjective_apply,
    Pi.basisFun_apply, BinaryTransvection.coordinate]

/-- Entrywise formula for the residual basis `p ⊗ e_j`. -/
theorem residualBasis_apply (p : ι → F)
    (hp : dotProduct p p = (1 : F)) (j k : Fin h) (i : ι) :
    (residualBasis p hp j : Address ι h) (i, k) =
      if k = j then p i else 0 := by
  rw [residualBasis_coe]
  simp [insert, BinaryTransvection.coordinate, Pi.single_apply]

/-- Orthonormality here is over the binary bilinear dot form: the Gram
    matrix of the residual basis is literally the identity. -/
theorem residualBasis_dot (p : ι → F)
    (hp : dotProduct p p = (1 : F)) (j k : Fin h) :
    dotProduct (residualBasis p hp j : Address ι h)
      (residualBasis p hp k : Address ι h) = if j = k then 1 else 0 := by
  rw [residualBasis_coe, residualBasis_coe, insert_dot_insert p hp,
    BinaryTransvection.coordinate_dot]
  simp [BinaryTransvection.coordinate, Pi.single_apply]

/-- One statement contains the centre-row geometry and exact directional count
    needed at every prefix size. -/
theorem row_certificate (p : ι → F) (hp : dotProduct p p = (1 : F)) :
    IsCompl (residual (h := h) p) (parent p) ∧
      parent (h := h) p = (residual (h := h) p).orthogonalBilin
        (BinaryTransvection.bilinearDot : _) ∧
      Module.finrank F (residual (h := h) p) = h ∧
      ∀ j k : Fin h,
        dotProduct (residualBasis p hp j : Address ι h)
          (residualBasis p hp k : Address ι h) = if j = k then 1 else 0 := by
  exact ⟨row_isCompl p hp, parent_eq_residual_orthogonal p,
    residual_finrank p hp, residualBasis_dot p hp⟩

end OAI.ExactFourier.CenterRowGeneral
