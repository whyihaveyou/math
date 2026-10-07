import OAI.Computability.FourierCircuit.CenterRowTransition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Generic side-row two-line certificate

This file isolates the linear-algebra content of a side transition. A prefix
unit line `p` contracts the first factor, producing the active space
`D = F₂^h`. If the old side label is `x` and the new label is orthogonal to
it, `y`, then the old row is the preimage of `span x` and the new row is the
preimage of `y⊥`. Their new directions are exactly the insertion of the pair
complement `(span {x,y})^⊥`, of dimension `h-2`.

The statement is independent of the network schedule and frame transport.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SideRowGeneral

abbrev F := ZMod 2
abbrev D (h : ℕ) := Fin h → F
abbrev E (h : ℕ) := Fin h → D h

/-- Fibrewise contraction against the prefix unit label. -/
abbrev projectP {h : ℕ} (p : Fin h → F) : E h →ₗ[F] D h :=
  CenterRowTransition.projectP p

/-- Tensor insertion along the prefix line. -/
abbrev insertP {h : ℕ} (p : Fin h → F) : D h →ₗ[F] E h :=
  CenterRowTransition.insertP p

abbrev line (x : D h) : Submodule F (D h) := F ∙ x

abbrev targetPerp (y : D h) : Submodule F (D h) :=
  (F ∙ y).orthogonalBilin (BinaryTransvection.bilinearDot : _)

abbrev pairPerp (x y : D h) : Submodule F (D h) :=
  (Submodule.span F ({x, y} : Set (D h))).orthogonalBilin
    (BinaryTransvection.bilinearDot : _)

/-- Side row before the transition. -/
abbrev L2 (p : Fin h → F) (x : D h) : Submodule F (E h) :=
  (line x).comap (projectP p)

/-- Side row after the transition. -/
abbrev L5 (p : Fin h → F) (y : D h) : Submodule F (E h) :=
  (targetPerp y).comap (projectP p)

/-- Insertion restricted to the two-label orthogonal complement. -/
def insertPair (p : Fin h → F) (x y : D h) :
    pairPerp x y →ₗ[F] E h :=
  (insertP p).comp (pairPerp x y).subtype

abbrev residual (p : Fin h → F) (x y : D h) : Submodule F (E h) :=
  LinearMap.range (insertPair p x y)

@[simp] theorem project_insertP {h : ℕ} (p : Fin h → F)
    (hp : dotProduct p p = (1 : F)) (d : D h) :
    projectP p (insertP p d) = d := by
  exact CenterRowTransition.projectP_insertP p hp d

/-- A pair complement vector is orthogonal to each of the two labels. -/
theorem mem_pairPerp_iff {h : ℕ} {x y z : D h} :
    z ∈ pairPerp x y ↔ dotProduct x z = 0 ∧ dotProduct y z = 0 := by
  rw [Submodule.mem_orthogonalBilin_span]
  constructor
  · intro hz
    constructor
    · exact hz (by simp)
    · exact hz (by simp)
  · intro hz q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact hz.1
    · exact hz.2

/-- A target line is nested in the new target complement. -/
theorem line_le_targetPerp {h : ℕ} {x y : D h}
    (hxy : dotProduct x y = 0) :
    line x ≤ targetPerp y := by
  change line x ≤ (F ∙ y).orthogonalBilin (BinaryTransvection.bilinearDot : _)
  rw [Submodule.orthogonalBilin_span_singleton]
  intro z hz
  rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
  simp only [LinearMap.mem_ker]
  change dotProduct y (a • x) = 0
  rw [dotProduct_smul]
  have hyx : dotProduct y x = 0 := by
    rw [dotProduct_comm]
    exact hxy
  simp [smul_eq_mul, hyx]

/-- The fibrewise old row is contained in the fibrewise new row. -/
theorem L2_le_L5 {h : ℕ} (p : Fin h → F) (x y : D h)
    (hxy : dotProduct x y = 0) :
    L2 p x ≤ L5 p y := by
  intro z hz
  rw [Submodule.mem_comap] at hz ⊢
  exact line_le_targetPerp hxy hz

/-- Inserting a pair-perpendicular active vector lands in the new row. -/
theorem residual_le_L5 {h : ℕ} (p : Fin h → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hxy : dotProduct x y = 0) :
    residual p x y ≤ L5 p y := by
  rintro z ⟨r, rfl⟩
  rw [Submodule.mem_comap]
  have hry : dotProduct y r.1 = 0 := (mem_pairPerp_iff).mp r.property |>.2
  change projectP p (insertPair p x y r) ∈
    (F ∙ y).orthogonalBilin (BinaryTransvection.bilinearDot : _)
  rw [Submodule.orthogonalBilin_span_singleton]
  change dotProduct y (projectP p (insertPair p x y r)) = 0
  change dotProduct y (projectP p (insertP p r.1)) = 0
  rw [project_insertP p hp]
  exact hry

/-- The old line and the pair complement form the active target complement. -/
theorem active_target_decomp {h : ℕ} (x y : D h)
    (hx : dotProduct x x = (1 : F)) (hxy : dotProduct x y = 0) :
    targetPerp y = line x ⊔ pairPerp x y := by
  simpa [targetPerp, line, pairPerp] using
    (BinaryTransvection.orthogonal_pair_decomp x y hx hxy)

/-- The side row after the transition is the old row plus the inserted pair
complement. -/
theorem side_row_decomp {h : ℕ} (p : Fin h → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = 0) :
    L5 p y = L2 p x ⊔ residual p x y := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_comap] at hz
    have hz' : projectP p z ∈ line x ⊔ pairPerp x y := by
      rw [← active_target_decomp x y hx hxy]
      exact hz
    rcases Submodule.mem_sup.mp hz' with ⟨u, hu, r, hr, hsum⟩
    let rr : pairPerp x y := ⟨r, hr⟩
    have hres : insertP p r ∈ residual p x y := by
      apply LinearMap.mem_range.mpr
      exact ⟨rr, by rfl⟩
    have hleft : z - insertP p r ∈ L2 p x := by
      rw [Submodule.mem_comap]
      have heq : projectP p (z - insertP p r) = u := by
        rw [map_sub, project_insertP p hp]
        rw [← hsum]
        abel
      rw [heq]
      exact hu
    apply Submodule.mem_sup.mpr
    exact ⟨z - insertP p r, hleft, insertP p r, hres, by abel⟩
  · apply sup_le
    · exact L2_le_L5 p x y hxy
    · exact residual_le_L5 p x y hp hxy

/-- The inserted residual is disjoint from the old row. -/
theorem L2_disjoint_residual {h : ℕ} (p : Fin h → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hxy : dotProduct x y = 0) :
    Disjoint (L2 p x) (residual p x y) := by
  rw [disjoint_iff]
  apply le_antisymm
  · intro z hz
    have hz2 : z ∈ L2 p x := hz.1
    have hzr : z ∈ residual p x y := hz.2
    rcases hzr with ⟨r, hr⟩
    have hline : projectP p z ∈ line x := hz2
    have hrproj : projectP p (insertPair p x y r) = r.1 := by
      change projectP p (insertP p r.1) = r.1
      exact project_insertP p hp r.1
    have hline' : projectP p (insertPair p x y r) ∈ line x := by
      rw [hr]
      exact hline
    have hrline : r.1 ∈ line x := by simpa [hrproj] using hline'
    have hrx : dotProduct x r.1 = 0 := (mem_pairPerp_iff).mp r.property |>.1
    have hzero : r.1 = 0 := by
      rcases Submodule.mem_span_singleton.mp hrline with ⟨a, ha⟩
      have hdot : dotProduct x (a • x) = 0 := by simpa [ha] using hrx
      have ha0 : a = 0 := by
        simpa [dotProduct_smul, smul_eq_mul, hx] using hdot
      have hz' : (0 : D h) = r.1 := by simpa [ha0] using ha
      exact hz'.symm
    have hvector : insertP p r.1 = 0 := by simp [hzero]
    rw [← hr]
    change insertP p r.1 = 0
    exact hvector
  · exact bot_le

/-- The two active coordinates seen by a side transition. -/
def pairMap {h : ℕ} (x y : D h) : D h →ₗ[F] F × F where
  toFun z := (dotProduct x z, dotProduct y z)
  map_add' z w := by
    apply Prod.ext <;> simp [dotProduct_add]
  map_smul' a z := by
    apply Prod.ext <;> simp [dotProduct_smul]

theorem pairMap_surjective {h : ℕ} (x y : D h)
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = 0) :
    Function.Surjective (pairMap x y) := by
  intro z
  rcases z with ⟨a, b⟩
  refine ⟨a • x + b • y, ?_⟩
  apply Prod.ext <;>
    simp [pairMap, dotProduct_add, dotProduct_smul, hx, hy, hxy,
      dotProduct_comm, smul_eq_mul]

theorem pairMap_ker {h : ℕ} (x y : D h) :
    LinearMap.ker (pairMap x y) = pairPerp x y := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_orthogonalBilin_span]
  change (dotProduct x z, dotProduct y z) = (0, 0) ↔ _
  constructor
  · intro hz q hq
    have hxz : dotProduct x z = 0 := by simpa using congrArg Prod.fst hz
    have hyz : dotProduct y z = 0 := by simpa using congrArg Prod.snd hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact hxz
    · exact hyz
  · intro hz
    exact Prod.ext (hz (by simp)) (hz (by simp))

theorem insertPair_injective {h : ℕ} (p : Fin h → F)
    (x y : D h) (hp : dotProduct p p = (1 : F)) :
    Function.Injective (insertPair p x y) := by
  intro a b hab
  apply Subtype.ext
  change a.1 = b.1
  apply CenterRowTransition.insertP_injective p hp
  change insertP p a.1 = insertP p b.1 at hab
  exact hab

/-- The inserted residual has active dimension `h-2`, whenever both labels
are unit and orthogonal.  The statement is meaningful for `2 ≤ h`; the
finite-dimensional calculation is left in natural-number form. -/
theorem residual_finrank {h : ℕ} (p : Fin h → F) (x y : D h)
    (hp : dotProduct p p = (1 : F))
    (hx : dotProduct x x = (1 : F))
    (hy : dotProduct y y = (1 : F))
    (hxy : dotProduct x y = 0) (hh : 2 ≤ h) :
    Module.finrank F (residual p x y) = h - 2 := by
  rw [show residual p x y = LinearMap.range (insertPair p x y) from rfl]
  rw [LinearMap.finrank_range_of_inj (insertPair_injective p x y hp)]
  let f := pairMap x y
  have hf : Function.Surjective f := pairMap_surjective x y hx hy hxy
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  have hker : LinearMap.ker f = pairPerp x y := pairMap_ker x y
  have hsum := f.finrank_range_add_finrank_ker
  rw [hrange] at hsum
  rw [← hker]
  simp [D, Module.finrank_pi] at hsum
  have heq : h = 2 + Module.finrank F (LinearMap.ker f) := hsum.symm
  omega

end SideRowGeneral
end ExactFourier
end OAI
