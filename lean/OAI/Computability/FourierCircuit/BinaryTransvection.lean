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

end BinaryTransvection
end ExactFourier
end OAI
