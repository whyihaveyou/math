import OAI.Computability.FourierCircuit.BinaryTransvection
import OAI.Computability.FourierCircuit.ComplexShearGateBridge

/-!
# Binary-frame to complex-coordinate boundary

The frame bookkeeping uses vectors over `ZMod 2`, while the scalar circuit
model uses complex coordinates.  There is no nonzero additive (hence no
linear) embedding `ZMod 2 → ℂ`: characteristic two forces the image of `1`
to satisfy `z+z=0`, and characteristic zero then forces `z=0`.

This file records that obstruction and the only local bridge used below:
when two binary summands are disjoint at every coordinate, the 0/1 support
map sends their binary sum to ordinary complex vector addition.  The latter
is a support identity, not a semantics theorem for a global circuit.
-/

namespace OAI
namespace ExactFourier
namespace BinaryComplexFrameMap

open BinaryTransvection

abbrev F2 := ZMod 2

/-- The pointwise support map, sending the two bits to `0` and `1`. -/
noncomputable def bitToComplex (b : F2) : ℂ := if b = 0 then 0 else 1

@[simp] theorem bitToComplex_zero : bitToComplex (0 : F2) = 0 := by
  simp [bitToComplex]

@[simp] theorem bitToComplex_one : bitToComplex (1 : F2) = 1 := by
  simp [bitToComplex]

@[simp] theorem bitToComplex_eq_zero_or_one (b : F2) :
    bitToComplex b = 0 ∨ bitToComplex b = 1 := by
  by_cases hb : b = 0
  · left
    simp [bitToComplex, hb]
  · right
    simp [bitToComplex, hb]

/-- Pointwise 0/1 support map from binary labels to complex vectors. -/
noncomputable def bitVectorToComplex {ι : Type*} (x : ι → F2) : ι → ℂ :=
  fun i => bitToComplex (x i)

@[simp] theorem bitVectorToComplex_apply {ι : Type*} (x : ι → F2) (i : ι) :
    bitVectorToComplex x i = bitToComplex (x i) := rfl

/-- A binary sum maps to ordinary addition whenever the two supports do not
overlap at a coordinate.  This is the exact finite support fact needed to
transport `t + coordinate w` when `t w = 0`. -/
theorem bitToComplex_add_of_not_both_one (a b : F2)
    (h : ¬ (a = 1 ∧ b = 1)) :
    bitToComplex (a + b) = bitToComplex a + bitToComplex b := by
  fin_cases a
  · fin_cases b
    · change (if (0 : F2) + 0 = 0 then 0 else 1) =
        (if (0 : F2) = 0 then 0 else 1) + (if (0 : F2) = 0 then 0 else 1)
      have hab : (0 : F2) + 0 = 0 := by decide
      simp [hab]
    · change (if (0 : F2) + 1 = 0 then 0 else 1) =
        (if (0 : F2) = 0 then 0 else 1) + (if (1 : F2) = 0 then 0 else 1)
      have hneq : (0 : F2) + 1 ≠ 0 := by decide
      have hone : (1 : F2) ≠ 0 := by decide
      simp [hneq, hone]
  · fin_cases b
    · change (if (1 : F2) + 0 = 0 then 0 else 1) =
        (if (1 : F2) = 0 then 0 else 1) + (if (0 : F2) = 0 then 0 else 1)
      have hneq : (1 : F2) + 0 ≠ 0 := by decide
      have hone : (1 : F2) ≠ 0 := by decide
      simp [hneq, hone]
    · exfalso
      apply h
      constructor <;> rfl

/-- The complex coordinate vector corresponding to one address. -/
def complexCoordinate {ι : Type*} [DecidableEq ι] (w : ι) : ι → ℂ :=
  fun i => if i = w then 1 else 0

/-- The coordinate label is disjoint from a unit vector away from that
coordinate, so its support map is an ordinary complex sum. -/
theorem bitVectorToComplex_add_coordinate {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → F2) (w : ι) (hw : t w = 0) :
    bitVectorToComplex (t + BinaryTransvection.coordinate w) =
      bitVectorToComplex t + complexCoordinate w := by
  funext i
  by_cases hi : i = w
  · subst i
    change bitToComplex (t w + BinaryTransvection.coordinate w w) =
      bitToComplex (t w) + complexCoordinate w w
    simp [BinaryTransvection.coordinate, complexCoordinate, hw]
  · have hnot : ¬ (t i = 1 ∧ BinaryTransvection.coordinate w i = 1) := by
      intro h
      have hzero : BinaryTransvection.coordinate w i ≠ 1 := by
        simp [BinaryTransvection.coordinate, hi]
      exact hzero h.2
    change bitToComplex ((t + BinaryTransvection.coordinate w) i) =
      bitToComplex (t i) + complexCoordinate w i
    rw [Pi.add_apply, bitToComplex_add_of_not_both_one _ _ hnot]
    simp [bitVectorToComplex, BinaryTransvection.coordinate, complexCoordinate, hi]

/-- Every additive map from `ZMod 2` to the characteristic-zero field `ℂ`
is zero.  Thus a binary frame label cannot be identified with a complex
coordinate through an additive or linear embedding. -/
theorem addMonoidHom_zmod_two_to_complex_zero (f : F2 →+ ℂ) : f = 0 := by
  have hsum : f (1 : F2) + f (1 : F2) = 0 := by
    calc
      f (1 : F2) + f (1 : F2) = f ((1 : F2) + 1) :=
        (f.map_add (1 : F2) 1).symm
      _ = f 0 := by rw [show (1 : F2) + 1 = 0 by decide]
      _ = 0 := f.map_zero
  have hmul : (2 : ℂ) * f (1 : F2) = 0 := by
    simpa [two_mul] using hsum
  have hone : f (1 : F2) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  ext b
  fin_cases b
  · exact f.map_zero
  · exact hone

/-- The same obstruction for an additive map into any characteristic-zero
field.  A future frame-compatible construction must therefore use a
non-additive encoding or a separate semantic invariant. -/
theorem addMonoidHom_zmod_two_to_charZero_zero
    {K : Type*} [Field K] [CharZero K]
    (f : F2 →+ K) : f = 0 := by
  have hsum : f (1 : F2) + f (1 : F2) = 0 := by
    calc
      f (1 : F2) + f (1 : F2) = f ((1 : F2) + 1) :=
        (f.map_add (1 : F2) 1).symm
      _ = f 0 := by rw [show (1 : F2) + 1 = 0 by decide]
      _ = 0 := f.map_zero
  have hmul : (2 : K) * f (1 : F2) = 0 := by
    simpa [two_mul] using hsum
  have hone : f (1 : F2) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  ext b
  fin_cases b
  · exact f.map_zero
  · exact hone

/-- Open compatibility premise for any attempted semantic bridge.  The
existing `ComplexShearGateBridge` discharges the scalar side once a complex
shear is supplied; this premise is the missing frame-to-coordinate statement.
It is intentionally not asserted by the binary algebra. -/
structure FrameToComplexShearPremise {ι : Type*} [Fintype ι]
    (u : ι → F2) (s : Shear ι) : Prop where
  support_encoding : bitVectorToComplex u = s.act (bitVectorToComplex u)
  frame_transport : ∀ x : ι → F2,
    bitVectorToComplex (BinaryTransvection.transvection u x) =
      s.act (bitVectorToComplex x)

/-! ## A concrete unit-shear test

The next two results separate a genuine local `Gate.add` identity from the
binary transvection used by the frame algebra.  The positive result is only
for a restricted, single-coordinate update and for inputs whose two binary
operands do not overlap.  The negative result is the smallest isotropic
transvection: its source coordinate is cleared, whereas a complex shear
always leaves its source coordinate available. -/

/-- A binary update which changes one destination by one source.  This is not
the full orthogonal transvection; it is the operation represented by one
elementary binary row update. -/
def binarySingleAdd {n : ℕ} (i j : Fin n) (x : Fin n → F2) : Fin n → F2 :=
  fun k => if k = i then x i + x j else x k

/-- The coefficient-one complex shear with the same ordered pair. -/
noncomputable def unitShear {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Shear (Fin n) :=
  ⟨i, j, hij, 1⟩

/-- On the disjoint-support domain, one binary single-coordinate update is
exactly the support-map image of a coefficient-one complex shear (`Gate.add`).
The disjointness hypothesis is essential: binary `1+1=0`, while complex
`1+1=2`. -/
theorem bitVectorToComplex_binarySingleAdd {n : ℕ} [DecidableEq (Fin n)]
    (i j : Fin n) (hij : i ≠ j) (x : Fin n → F2)
    (hdisjoint : ¬ (x i = 1 ∧ x j = 1)) :
    bitVectorToComplex (binarySingleAdd i j x) =
      (unitShear i j hij).act (bitVectorToComplex x) := by
  funext k
  by_cases hki : k = i
  · subst k
    simpa [binarySingleAdd, bitVectorToComplex, unitShear, Shear.act] using
      bitToComplex_add_of_not_both_one (x i) (x j) hdisjoint
  · simp [binarySingleAdd, unitShear, Shear.act, hki]

private def twoOnes : Fin 2 → F2 := fun _ => 1

/-- The nonzero isotropic vector `(1,1)` sends the first coordinate basis
vector to the second one under the binary transvection. -/
theorem twoOnes_transvection_coordinate_zero :
    BinaryTransvection.transvection twoOnes (BinaryTransvection.coordinate (0 : Fin 2)) =
      BinaryTransvection.coordinate (1 : Fin 2) := by
  rw [BinaryTransvection.transvection_apply]
  have hdot : dotProduct twoOnes (BinaryTransvection.coordinate (0 : Fin 2)) =
      (1 : F2) := by
    rw [dotProduct_comm, BinaryTransvection.coordinate_dot]
    simp [twoOnes]
  rw [hdot]
  funext k
  fin_cases k <;> simp [twoOnes, BinaryTransvection.coordinate] <;> decide

/-- No single complex shear, including the coefficient-one case, can carry
the support-map image of this `Fin 2` binary transvection.  At input
`coordinate 0`, the binary transvection clears coordinate `0`; a complex
shear always leaves coordinate `0` equal to its original value when `0` is a
source, and when it is the destination it adds a source coordinate that is
zero. -/
theorem no_fin2_shear_support_transport (s : Shear (Fin 2)) :
    ¬ (∀ x : Fin 2 → F2,
      bitVectorToComplex (BinaryTransvection.transvection twoOnes x) =
        s.act (bitVectorToComplex x)) := by
  intro htransport
  have hleft :
      bitVectorToComplex
          (BinaryTransvection.transvection twoOnes
            (BinaryTransvection.coordinate (0 : Fin 2))) (0 : Fin 2) = 0 := by
    rw [twoOnes_transvection_coordinate_zero]
    simp [bitVectorToComplex, bitToComplex, BinaryTransvection.coordinate]
  have hright :
      s.act (bitVectorToComplex (BinaryTransvection.coordinate (0 : Fin 2)))
          (0 : Fin 2) = 1 := by
    by_cases hi : (0 : Fin 2) = s.i
    · have hj0 : s.j ≠ (0 : Fin 2) := by
        intro hj
        apply s.hij
        exact hi.symm.trans hj.symm
      simp [Shear.act, bitVectorToComplex, bitToComplex,
        BinaryTransvection.coordinate, hi, hj0, s.hij]
    · simp [Shear.act, bitVectorToComplex, bitToComplex,
        BinaryTransvection.coordinate, hi]
  have heq := congr_fun (htransport (BinaryTransvection.coordinate (0 : Fin 2)))
      (0 : Fin 2)
  rw [hleft, hright] at heq
  norm_num at heq

/-! A scalar-gate corollary of the preceding support obstruction.  The
`UnitShearWitness` is an actual `LinearDAG` containing one `Gate.add`; its
`computes` field identifies the resulting scalar program with the complex
shear matrix.  Therefore even this concrete one-gate realization cannot be
used as a global semantic implementation of the binary transvection.  This
is the smallest gate-level attachment of the binary/frame no-go; it does not
exclude a different multi-gate matrix or a non-support frame invariant. -/

theorem no_unitShearWitness_fin2_support_transport
    (s : Shear (Fin 2))
    (W : ComplexShearGateBridge.UnitShearWitness 2 s) :
    ¬ (∀ x : Fin 2 → F2,
      bitVectorToComplex (BinaryTransvection.transvection twoOnes x) =
        W.circuit.eval (bitVectorToComplex x)) := by
  intro htransport
  apply no_fin2_shear_support_transport s
  intro x
  calc
    bitVectorToComplex (BinaryTransvection.transvection twoOnes x) =
        W.circuit.eval (bitVectorToComplex x) := htransport x
    _ = s.toMatrix.mulVec (bitVectorToComplex x) := W.computes _
    _ = s.act (bitVectorToComplex x) :=
      (Shear.act_eq_mulVec s (bitVectorToComplex x)).symm

end BinaryComplexFrameMap
end ExactFourier
end OAI
