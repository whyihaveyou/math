import OAI.Computability.FourierCircuit.BinaryTransvection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# Generic centre-row direction certificate

The centre transition is a product-space statement.  Write `E ⊗ D` as the
function space `Fin h → D`, where `D = Fin h → F₂`.  A unit first-factor line
can be put at a coordinate `w`; its tensor with `D` is the range of the
coordinate insertion map.  The complementary row is the kernel of the
coordinate projection.  This file proves that these two rows are a direct
sum and that the removed residual has dimension `h`.

The coordinate normalization is supplied by `BinaryTransvection`; transporting
this statement back to an arbitrary unit line and identifying every paper
frame label with the corresponding tensor-product submodule remains a separate
network-level obligation.
-/

namespace OAI
namespace ExactFourier
namespace CenterRowTransition

abbrev F := ZMod 2
abbrev D (h : ℕ) := Fin h → F
abbrev E (h : ℕ) := Fin h → D h

/-- Projection to one first-factor coordinate. -/
def project (h : ℕ) (w : Fin h) : E h →ₗ[F] D h :=
  LinearMap.proj w

/-- Insertion of an entire `D`-slice at first-factor coordinate `w`. -/
def insert (h : ℕ) (w : Fin h) : D h →ₗ[F] E h :=
  LinearMap.single F (fun _ : Fin h => D h) w

abbrev centerParent (h : ℕ) (w : Fin h) : Submodule F (E h) :=
  LinearMap.ker (project h w)

abbrev centerResidual (h : ℕ) (w : Fin h) : Submodule F (E h) :=
  LinearMap.range (insert h w)

/-- Projection onto the inserted slice, viewed as a map into that submodule. -/
def sliceProjection (h : ℕ) (w : Fin h) : E h →ₗ[F] centerResidual h w where
  toFun x := ⟨insert h w (project h w x), by
    exact LinearMap.mem_range_self (insert h w) (project h w x)⟩
  map_add' x y := by
    apply Subtype.ext
    change insert h w (project h w (x + y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a x := by
    apply Subtype.ext
    simp [project, insert]

theorem sliceProjection_fix (h : ℕ) (w : Fin h)
    (x : centerResidual h w) : sliceProjection h w x = x := by
  apply Subtype.ext
  rcases x with ⟨x, ⟨d, rfl⟩⟩
  simp [sliceProjection, project, insert]

/-- The row-3 to row-4 centre transition is a direct-sum decomposition. -/
theorem center_row_isCompl (h : ℕ) (w : Fin h) :
    IsCompl (centerResidual h w) (centerParent h w) := by
  have hk : LinearMap.ker (sliceProjection h w) = centerParent h w := by
    ext x
    constructor
    · intro hx
      have hx' : insert h w (project h w x) = 0 := by
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have he := congrArg (fun z : E h => z w) hx'
      simpa [project, insert] using he
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change insert h w (project h w x) = 0
      rw [LinearMap.mem_ker.mp hx, map_zero]
  rw [← hk]
  exact LinearMap.isCompl_of_proj (sliceProjection_fix h w)

 theorem insert_injective (h : ℕ) (w : Fin h) :
    Function.Injective (insert h w) := by
  intro x y hxy
  apply_fun project h w at hxy
  simpa [project, insert] using hxy

/-- The removed `P ⊗ D` slice has exactly `h` binary coordinates. -/
theorem center_residual_finrank (h : ℕ) (w : Fin h) :
    Module.finrank F (centerResidual h w) = h := by
  rw [show centerResidual h w = LinearMap.range (insert h w) from rfl]
  rw [LinearMap.finrank_range_of_inj (insert_injective h w)]
  simpa [D] using (Module.finrank_pi F : Module.finrank F (Fin h → F) = Fintype.card (Fin h))

/-- Combined direction certificate used by a centre-stage cost audit. -/
theorem center_row_certificate (h : ℕ) (w : Fin h) :
    IsCompl (centerResidual h w) (centerParent h w) ∧
      Module.finrank F (centerResidual h w) = h := by
  exact ⟨center_row_isCompl h w, center_residual_finrank h w⟩

end CenterRowTransition
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace CenterRowTransition

/-! ### Arbitrary unit first-factor label -/

/-- The first-factor functional, with `p` as its unit normal. -/
def firstFunctional {h : ℕ} (p : Fin h → F) :
    (Fin h → F) →ₗ[F] F :=
  BinaryTransvection.bilinearDot p

abbrev firstComplement {h : ℕ} (p : Fin h → F) :
    Submodule F (Fin h → F) :=
  LinearMap.ker (firstFunctional p)

theorem firstComplement_eq_orthogonal {h : ℕ} (p : Fin h → F) :
    firstComplement p =
      ((F) ∙ p).orthogonalBilin
        (BinaryTransvection.bilinearDot : _) := by
  ext q
  change dotProduct p q = 0 ↔ _
  rw [Submodule.orthogonalBilin_span_singleton]
  rfl

/-- Fibrewise evaluation against `p`; this is the `B ⊗ D` parent row. -/
def projectP {h : ℕ} (p : Fin h → F) :
    E h →ₗ[F] D h where
  toFun x := fun j => dotProduct p (fun i => x i j)
  map_add' x y := by
    funext j
    change dotProduct p ((fun i => x i j) + (fun i => y i j)) = _
    rw [dotProduct_add]
    rfl
  map_smul' a x := by
    funext j
    change dotProduct p (a • (fun i => x i j)) = _
    rw [dotProduct_smul]
    rfl

/-- Insert a `D`-slice along the first-factor label `p`; this is `P ⊗ D`. -/
def insertP {h : ℕ} (p : Fin h → F) :
    D h →ₗ[F] E h where
  toFun d := fun i j => p i * d j
  map_add' x y := by
    ext i j
    simp [mul_add]
  map_smul' a x := by
    ext i j
    simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

theorem projectP_insertP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) (d : D h) :
    projectP p (insertP p d) = d := by
  funext j
  have hfun : (fun i => p i * d j) = (d j) • p := by
    funext i
    simp [smul_eq_mul, mul_comm]
  change dotProduct p (fun i => p i * d j) = d j
  rw [hfun, dotProduct_smul, hp]
  simp

def sliceProjectionP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) :
    E h →ₗ[F] LinearMap.range (insertP p) where
  toFun x := ⟨insertP p (projectP p x),
    LinearMap.mem_range_self (insertP p) (projectP p x)⟩
  map_add' x y := by
    apply Subtype.ext
    change insertP p (projectP p (x + y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a x := by
    apply Subtype.ext
    change insertP p (projectP p (a • x)) = _
    rw [map_smul, map_smul]
    rfl

theorem sliceProjectionP_fix {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F))
    (x : LinearMap.range (insertP p)) :
    sliceProjectionP p hp x = x := by
  apply Subtype.ext
  rcases x with ⟨x, ⟨d, rfl⟩⟩
  simp [sliceProjectionP, projectP_insertP p hp]

theorem insertP_injective {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) :
    Function.Injective (insertP p) := by
  intro x y hxy
  apply_fun projectP p at hxy
  simpa [projectP_insertP p hp] using hxy

/-- The centre transition for an arbitrary unit label `p`. -/
theorem center_row_isComplP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) :
    IsCompl (LinearMap.range (insertP p)) (LinearMap.ker (projectP p)) := by
  have hk : LinearMap.ker (sliceProjectionP p hp) = LinearMap.ker (projectP p) := by
    ext x
    constructor
    · intro hx
      have hx' : insertP p (projectP p x) = 0 := by
        exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have he := congrArg (projectP p) hx'
      simpa [projectP_insertP p hp] using he
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change insertP p (projectP p x) = 0
      rw [LinearMap.mem_ker.mp hx, map_zero]
  rw [← hk]
  exact LinearMap.isCompl_of_proj (sliceProjectionP_fix p hp)

theorem center_residual_finrankP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) :
    Module.finrank F (LinearMap.range (insertP p)) = h := by
  rw [LinearMap.finrank_range_of_inj (insertP_injective p hp)]
  simpa [D] using (Module.finrank_pi F : Module.finrank F (Fin h → F) = Fintype.card (Fin h))

theorem center_parent_fibrewise {h : ℕ} (p : Fin h → F) (x : E h) :
    x ∈ LinearMap.ker (projectP p) ↔
      ∀ j : Fin h, (fun i => x i j) ∈ firstComplement p := by
  constructor
  · intro hx j
    apply LinearMap.mem_ker.mpr
    have hx0 := LinearMap.mem_ker.mp hx
    exact congrFun hx0 j
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext j
    change dotProduct p (fun i => x i j) = 0
    exact LinearMap.mem_ker.mp (hx j)

/-- Generic row 3→4 certificate: the parent is the fibrewise complement
`B ⊗ D`, the removed residual is `P ⊗ D`, and its dimension is `h`. -/
theorem center_row_certificateP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) :
    IsCompl (LinearMap.range (insertP p)) (LinearMap.ker (projectP p)) ∧
      Module.finrank F (LinearMap.range (insertP p)) = h := by
  exact ⟨center_row_isComplP p hp, center_residual_finrankP p hp⟩

end CenterRowTransition
end ExactFourier
end OAI
