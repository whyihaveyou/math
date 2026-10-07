import OAI.Computability.FourierCircuit.FrameLabels
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.StdBasis

/-!
# Explicit orthogonal coordinate changes over F₂

An isotropic transvection `x ↦ x + (u · x)u` is an involutive
dot-product isometry.  When a unit vector `t` has a zero coordinate `w`,
take `u = t + e_w`: this maps the coordinate vector `e_w` to `t`.
The construction supplies explicit orthogonal coordinates for the line
complements used by the frame audit, without appealing to a classification
of symmetric bilinear forms in characteristic two.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace BinaryTransvection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bilinearDot :
    (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun v w => dotProduct v w)
    (by intro v₁ v₂ w; simp [dotProduct, Finset.sum_add_distrib, add_mul])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_assoc])
    (by intro v w₁ w₂; simp [dotProduct, Finset.sum_add_distrib, mul_add])
    (by intro a v w; simp [dotProduct, Finset.mul_sum, mul_left_comm])

def transvection (u : ι → ZMod 2) :
    (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun x := x + dotProduct u x • u
  map_add' x y := by
    simp only [dotProduct_add, add_smul]
    abel
  map_smul' a x := by
    simp only [dotProduct_smul, smul_add, smul_smul, RingHom.id_apply]
    simp [smul_eq_mul, mul_assoc]

theorem transvection_apply (u x : ι → ZMod 2) :
    transvection u x = x + dotProduct u x • u := rfl

theorem transvection_involutive (u : ι → ZMod 2)
    (hu : dotProduct u u = 0) : Function.Involutive (transvection u) := by
  intro x
  simp only [transvection_apply, dotProduct_add, dotProduct_smul, hu,
    smul_zero, add_zero]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem transvection_dot (u x y : ι → ZMod 2)
    (hu : dotProduct u u = 0) :
    dotProduct (transvection u x) (transvection u y) = dotProduct x y := by
  simp only [transvection_apply, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hu, smul_zero, add_zero, smul_eq_mul]
  rw [dotProduct_comm x u]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  simp [h2]

def transvectionEquiv (u : ι → ZMod 2) (hu : dotProduct u u = 0) :
    (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) where
  toLinearMap := transvection u
  invFun := transvection u
  left_inv := transvection_involutive u hu
  right_inv := transvection_involutive u hu

def coordinate (w : ι) : ι → ZMod 2 := Pi.single w 1

theorem coordinate_dot (w : ι) (x : ι → ZMod 2) :
    dotProduct (coordinate w) x = x w := by
  simp [coordinate, single_dotProduct]

theorem dot_coordinate (w : ι) (x : ι → ZMod 2) :
    dotProduct x (coordinate w) = x w := by
  rw [dotProduct_comm, coordinate_dot]

theorem unit_shift_isotropic (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) :
    dotProduct (t + coordinate w) (t + coordinate w) = 0 := by
  simp only [add_dotProduct, dotProduct_add, ht, coordinate_dot, dot_coordinate, hw]
  have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  simp [h2, coordinate, CharTwo.add_self_eq_zero]

theorem unit_shift_maps_coordinate (t : ι → ZMod 2) (w : ι)
    (hw : t w = 0) :
    transvection (t + coordinate w) (coordinate w) = t := by
  rw [transvection_apply, dot_coordinate]
  simp only [Pi.add_apply, hw, coordinate, Pi.single_eq_same, zero_add, one_smul]
  ext i
  simp only [Pi.add_apply]
  rw [add_comm (t i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

def unitCoordinateEquiv (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) :
    (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
  transvectionEquiv (t + coordinate w) (unit_shift_isotropic t w ht hw)

theorem unitCoordinateEquiv_dot (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) (x y : ι → ZMod 2) :
    dotProduct (unitCoordinateEquiv t w ht hw x)
      (unitCoordinateEquiv t w ht hw y) = dotProduct x y :=
  transvection_dot _ _ _ (unit_shift_isotropic t w ht hw)

theorem unitCoordinateEquiv_coordinate (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) :
    unitCoordinateEquiv t w ht hw (coordinate w) = t :=
  unit_shift_maps_coordinate t w hw

theorem unitCoordinateEquiv_unit (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) :
    unitCoordinateEquiv t w ht hw t = coordinate w := by
  change transvection (t + coordinate w) t = coordinate w
  rw [transvection_apply]
  have hdot : dotProduct (t + coordinate w) t = 1 := by
    simp [add_dotProduct, coordinate_dot, ht, hw]
  rw [hdot]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul,
    coordinate, Pi.single_apply]
  by_cases hi : i = w
  · subst i
    simp [hw]
  · simp [hi, CharTwo.add_self_eq_zero]

theorem unitCoordinateEquiv_fix (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0)
    (q : ι → ZMod 2) (hqt : dotProduct t q = 0) (hqw : q w = 0) :
    unitCoordinateEquiv t w ht hw q = q := by
  change transvection (t + coordinate w) q = q
  rw [transvection_apply]
  have hdot : dotProduct (t + coordinate w) q = 0 := by
    simp [add_dotProduct, coordinate_dot, hqt, hqw]
  rw [hdot]
  simp

def coordinateEval (w : ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := x w
  map_add' x y := by simp
  map_smul' a x := by simp

def coordinateHyperplane (w : ι) : Submodule (ZMod 2) (ι → ZMod 2) :=
  (coordinateEval w).ker

theorem unitCoordinateEquiv_dot_coordinate (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) (x : ι → ZMod 2) :
    dotProduct t (unitCoordinateEquiv t w ht hw x) = x w := by
  calc
    dotProduct t (unitCoordinateEquiv t w ht hw x) =
        dotProduct (unitCoordinateEquiv t w ht hw (coordinate w))
          (unitCoordinateEquiv t w ht hw x) := by
            rw [unitCoordinateEquiv_coordinate]
    _ = dotProduct (coordinate w) x :=
      unitCoordinateEquiv_dot t w ht hw (coordinate w) x
    _ = x w := coordinate_dot w x

theorem unitCoordinateEquiv_comap_orthogonal (t : ι → ZMod 2) (w : ι)
    (ht : dotProduct t t = 1) (hw : t w = 0) :
    (((ZMod 2) ∙ t).orthogonalBilin (bilinearDot : _)).comap
        (unitCoordinateEquiv t w ht hw).toLinearMap = coordinateHyperplane w := by
  ext x
  rw [Submodule.mem_comap]
  rw [Submodule.orthogonalBilin_span_singleton]
  change bilinearDot t (unitCoordinateEquiv t w ht hw x) = 0 ↔ _
  change dotProduct t (unitCoordinateEquiv t w ht hw x) = 0 ↔ x w = 0
  rw [unitCoordinateEquiv_dot_coordinate t w ht hw x]

def coordinateHyperplaneTwo (w z : ι) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  coordinateHyperplane w ⊓ coordinateHyperplane z

def twoCoordinateEquiv (x y : ι → ZMod 2) (w z : ι)
    (hx : dotProduct x x = 1) (hy : dotProduct y y = 1)
    (hxw : x w = 0) (hyz : y z = 0) :
    (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
  (unitCoordinateEquiv x w hx hxw).trans
    (unitCoordinateEquiv y z hy hyz)

theorem twoCoordinateEquiv_dot (x y : ι → ZMod 2) (w z : ι)
    (hx : dotProduct x x = 1) (hy : dotProduct y y = 1)
    (hxw : x w = 0) (hyz : y z = 0) (a b : ι → ZMod 2) :
    dotProduct (twoCoordinateEquiv x y w z hx hy hxw hyz a)
      (twoCoordinateEquiv x y w z hx hy hxw hyz b) = dotProduct a b := by
  change dotProduct
      (unitCoordinateEquiv y z hy hyz (unitCoordinateEquiv x w hx hxw a))
      (unitCoordinateEquiv y z hy hyz (unitCoordinateEquiv x w hx hxw b)) = _
  rw [unitCoordinateEquiv_dot y z hy hyz]
  exact unitCoordinateEquiv_dot x w hx hxw a b

theorem twoCoordinateEquiv_x (x y : ι → ZMod 2) (w z : ι)
    (hx : dotProduct x x = 1) (hy : dotProduct y y = 1)
    (hxy : dotProduct x y = 0) (hxw : x w = 0)
    (hyw : y w = 0) (hyz : y z = 0) (hzw : z ≠ w) :
    twoCoordinateEquiv x y w z hx hy hxw hyz x = coordinate w := by
  change unitCoordinateEquiv y z hy hyz
      (unitCoordinateEquiv x w hx hxw x) = coordinate w
  rw [unitCoordinateEquiv_unit x w hx hxw]
  apply unitCoordinateEquiv_fix y z hy hyz (coordinate w)
  · rw [dot_coordinate]
    exact hyw
  · simp [coordinate, hzw]

theorem twoCoordinateEquiv_y (x y : ι → ZMod 2) (w z : ι)
    (hx : dotProduct x x = 1) (hy : dotProduct y y = 1)
    (hxy : dotProduct x y = 0) (hxw : x w = 0)
    (hyw : y w = 0) (hyz : y z = 0) (hzw : z ≠ w) :
    twoCoordinateEquiv x y w z hx hy hxw hyz y = coordinate z := by
  change unitCoordinateEquiv y z hy hyz
      (unitCoordinateEquiv x w hx hxw y) = coordinate z
  rw [unitCoordinateEquiv_fix x w hx hxw y hxy hyw]
  exact unitCoordinateEquiv_unit y z hy hyz

theorem twoCoordinateEquiv_comap_orthogonal (x y : ι → ZMod 2) (w z : ι)
    (hx : dotProduct x x = 1) (hy : dotProduct y y = 1)
    (hxy : dotProduct x y = 0) (hxw : x w = 0)
    (hyw : y w = 0) (hyz : y z = 0) (hzw : z ≠ w) :
    (coordinateHyperplaneTwo w z).comap
        (twoCoordinateEquiv x y w z hx hy hxw hyz).toLinearMap =
      (Submodule.span (ZMod 2) ({x, y} : Set (ι → ZMod 2))).orthogonalBilin
        (bilinearDot : _) := by
  ext q
  rw [Submodule.mem_comap]
  constructor
  · intro hq
    have hwq : (twoCoordinateEquiv x y w z hx hy hxw hyz q) w = 0 := by
      exact (show twoCoordinateEquiv x y w z hx hy hxw hyz q ∈
          coordinateHyperplane w from hq.1)
    have hzq : (twoCoordinateEquiv x y w z hx hy hxw hyz q) z = 0 := by
      exact (show twoCoordinateEquiv x y w z hx hy hxw hyz q ∈
          coordinateHyperplane z from hq.2)
    have hxq : dotProduct x q = 0 := by
      calc
        dotProduct x q = dotProduct
            (twoCoordinateEquiv x y w z hx hy hxw hyz x)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_dot]
        _ = dotProduct (coordinate w)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_x x y w z hx hy hxy hxw hyw hyz hzw]
        _ = 0 := by rw [coordinate_dot, hwq]
    have hyq : dotProduct y q = 0 := by
      calc
        dotProduct y q = dotProduct
            (twoCoordinateEquiv x y w z hx hy hxw hyz y)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_dot]
        _ = dotProduct (coordinate z)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_y x y w z hx hy hxy hxw hyw hyz hzw]
        _ = 0 := by rw [coordinate_dot, hzq]
    rw [Submodule.mem_orthogonalBilin_span]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hxq
    · exact hyq
  · intro hq
    rw [Submodule.mem_orthogonalBilin_span] at hq
    have hxq : dotProduct x q = 0 := hq (by simp)
    have hyq : dotProduct y q = 0 := hq (by simp)
    constructor
    · change (twoCoordinateEquiv x y w z hx hy hxw hyz q) w = 0
      calc
        (twoCoordinateEquiv x y w z hx hy hxw hyz q) w =
            dotProduct (coordinate w)
              (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
                rw [coordinate_dot]
        _ = dotProduct
            (twoCoordinateEquiv x y w z hx hy hxw hyz x)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_x x y w z hx hy hxy hxw hyw hyz hzw]
        _ = dotProduct x q := by
          rw [twoCoordinateEquiv_dot]
        _ = 0 := hxq
    · change (twoCoordinateEquiv x y w z hx hy hxw hyz q) z = 0
      calc
        (twoCoordinateEquiv x y w z hx hy hxw hyz q) z =
            dotProduct (coordinate z)
              (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
                rw [coordinate_dot]
        _ = dotProduct
            (twoCoordinateEquiv x y w z hx hy hxw hyz y)
            (twoCoordinateEquiv x y w z hx hy hxw hyz q) := by
              rw [twoCoordinateEquiv_y x y w z hx hy hxy hxw hyw hyz hzw]
        _ = dotProduct y q := by
          rw [twoCoordinateEquiv_dot]
        _ = 0 := hyq

theorem orthogonal_pair_decomp (x y : ι → ZMod 2)
    (hx : dotProduct x x = 1) (hxy : dotProduct x y = 0) :
    ((ZMod 2) ∙ y).orthogonalBilin (bilinearDot : _) =
      (ZMod 2) ∙ x ⊔
        (Submodule.span (ZMod 2) ({x, y} : Set (ι → ZMod 2))).orthogonalBilin
          (bilinearDot : _) := by
  ext v
  constructor
  · intro hv
    rw [Submodule.orthogonalBilin_span_singleton] at hv
    have hyv : dotProduct y v = 0 := LinearMap.mem_ker.mp hv
    let a : ZMod 2 := dotProduct x v
    let r : ι → ZMod 2 := v + a • x
    have hrx : dotProduct x r = 0 := by
      dsimp [r, a]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hx, mul_one]
      exact CharTwo.add_self_eq_zero _
    have hry : dotProduct y r = 0 := by
      dsimp [r, a]
      have hyx : dotProduct y x = 0 := by
        rw [dotProduct_comm]
        exact hxy
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul, hyx, hyv]
    have hrpair : r ∈
        (Submodule.span (ZMod 2) ({x, y} : Set (ι → ZMod 2))).orthogonalBilin
          (bilinearDot : _) := by
      rw [Submodule.mem_orthogonalBilin_span]
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact hrx
      · exact hry
    have hvdecomp : v = a • x + r := by
      dsimp [r]
      ext i
      calc
        v i = v i + (a * x i + a * x i) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
        _ = a * x i + (v i + a * x i) := by ring
    rw [hvdecomp]
    apply Submodule.mem_sup.mpr
    exact ⟨a • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x),
      r, hrpair, rfl⟩
  · intro hv
    rw [Submodule.orthogonalBilin_span_singleton]
    change dotProduct y v = 0
    rcases Submodule.mem_sup.mp hv with ⟨u, hu, r, hr, rfl⟩
    rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
    have hyr : dotProduct y r = 0 := by
      rw [Submodule.mem_orthogonalBilin_span] at hr
      exact hr (by simp)
    have hyx : dotProduct y x = 0 := by
      rw [dotProduct_comm]
      exact hxy
    simp [dotProduct_add, dotProduct_smul, smul_eq_mul, hyx, hyr]

end BinaryTransvection
end ExactFourier
end OAI
