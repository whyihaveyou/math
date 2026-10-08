import OAI.Computability.FourierCircuit.ArbitraryTwoFrameCover
import OAI.Computability.FourierCircuit.BinaryComplexFrameMap
import OAI.Computability.FourierCircuit.BinaryAddressPermutation
import OAI.Computability.FourierCircuit.AddressPhaseConjugation
import OAI.Computability.FourierCircuit.CenterBoundaryTensorLift
import Mathlib.Tactic

/-!
# Dense two-frame bridge and its gate-level boundary

`ArbitraryTwoFrameCover` gives the finite binary cover
`u = e₀`, `w = 1 + e₀` at even active width.  This file records the
strongest bridge currently available for that pair:

* the isotropic direction `1` gives a genuine binary orthogonal equivalence
  swapping the two active labels;
* its fibrewise lift is an address permutation, hence a free monomial matrix;
* the tempting support-map interpretation cannot be charged as one complex
  shear: on the coordinate input, the binary swap clears coordinate `0`, while
  every complex shear leaves that coordinate equal to `1`.

Consequently the two-frame route ledger remains conditional.  A physical
one-direction charge needs a separate `Phi`-ratio/factorisation theorem and a
frame-preserving scalar gate schedule; the binary address permutation alone
supplies neither.
-/

namespace OAI
namespace ExactFourier
namespace DenseTwoFrameComplexBridge

open ArbitraryTwoFrameCover
open FrameLabels
open BinaryTransvection
open BinaryComplexFrameMap
open BinaryAddressPermutation
open AddressPhaseConjugation
open CenterBoundaryTensorLift

abbrev F2 := ZMod 2
abbrev Active (h : ℕ) := Fin h → F2
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F2

/-- The dense complement label is zero at the anchored coordinate. -/
theorem denseComplement_zero {h : ℕ} (hh : 1 ≤ h) :
    denseComplementLabel (h := h) hh (zeroIndex hh) = 0 := by
  have hone : (1 : F2) + 1 = 0 := CharP.cast_eq_zero (ZMod 2) 2
  simp [denseComplementLabel, allOnes, unitLabel, zeroIndex,
    TripleSpan.basisVec, hone]

/-- The all-ones direction is isotropic at even active width. -/
theorem allOnes_isotropic {h : ℕ} (heven : Even h) :
    dotProduct (allOnes (h := h)) (allOnes (h := h)) = (0 : F2) := by
  classical
  simp only [allOnes, dotProduct, mul_one]
  rw [Finset.sum_const]
  simp only [Finset.card_fin]
  obtain ⟨k, hk⟩ := heven
  rw [hk, nsmul_eq_mul, mul_one, Nat.cast_add]
  have htwo : (2 : F2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  calc
    (k : F2) + k = (2 : F2) * k := by ring
    _ = 0 := by rw [htwo, zero_mul]

/-- The binary isotropic transvection induced by the dense pair. -/
noncomputable def denseSwap (h : ℕ) (hh : 2 ≤ h) (heven : Even h) :
    Active h ≃ₗ[F2] Active h :=
  unitCoordinateEquiv
    (denseComplementLabel (h := h) (by omega : 1 ≤ h))
    (zeroIndex (by omega : 1 ≤ h))
    (denseComplementLabel_unit (h := h) (by omega) heven)
    (denseComplement_zero (h := h) (by omega))

/-- The dense swap sends the anchored coordinate to the dense label. -/
theorem denseSwap_coordinate {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    denseSwap h hh heven (coordinate (zeroIndex (by omega : 1 ≤ h))) =
      denseComplementLabel (h := h) (by omega : 1 ≤ h) := by
  exact unitCoordinateEquiv_coordinate _ _ _ _

/-- The dense swap sends the dense label back to the anchored coordinate. -/
theorem denseSwap_dense {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    denseSwap h hh heven
      (denseComplementLabel (h := h) (by omega : 1 ≤ h)) =
      coordinate (zeroIndex (by omega : 1 ≤ h)) := by
  exact unitCoordinateEquiv_unit _ _ _ _

/-- The fibrewise dense swap is an exact binary address isometry. -/
theorem denseSwap_lift_dot {ι : Type*} [Fintype ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h)
    (z z' : Address ι h) :
    dotProduct
        (lift (denseSwap h hh heven) z)
        (lift (denseSwap h hh heven) z') =
      dotProduct z z' := by
  apply lift_dot
  intro a b
  exact unitCoordinateEquiv_dot _ _ _ _ a b

/-- The dense swap induces only free monomial address work. -/
theorem denseSwap_address_monomial {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h) :
    MonomialMatrix
      (BinaryAddressPermutation.matrix (ι := ι × Fin h)
        (lift (denseSwap h hh heven))) := by
  exact BinaryAddressPermutation.matrix_monomial
    (lift (denseSwap h hh heven))

/-- The dense swap has an exact complex matrix-unit semantics after lifting
the binary map to addresses.  This is the concrete free-address bridge: no
support-map embedding of `ZMod 2` into `ℂ` is used. -/
theorem denseSwap_matrix_conj_single
    {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h)
    (a b : Address ι h) :
    BinaryAddressPermutation.matrix
        (ι := ι × Fin h)
        (lift (ι := ι) (denseSwap h hh heven)) * Matrix.single a b (1 : ℂ) *
        (BinaryAddressPermutation.matrix
          (ι := ι × Fin h)
          (lift (ι := ι) (denseSwap h hh heven)))⁻¹ =
      Matrix.single
        (BinaryAddressPermutation.induced
          (lift (ι := ι) (denseSwap h hh heven)) a)
        (BinaryAddressPermutation.induced
          (lift (ι := ι) (denseSwap h hh heven)) b) 1 := by
  exact BinaryAddressPermutation.matrix_conj_single
    (lift (ι := ι) (denseSwap h hh heven)) a b

/-- The same free address change only relabels an arbitrary complex diagonal
phase profile.  A future concrete Walsh `Phi` construction can use this
identity as its address-change premise; it does not provide the charged
directional factorization. -/
theorem denseSwap_phaseDiagonal_conj
    {ι : Type 0} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (hh : 2 ≤ h) (heven : Even h)
    (q : Address ι h → ℂ) :
    BinaryAddressPermutation.matrix
        (ι := ι × Fin h) (lift (ι := ι) (denseSwap h hh heven)) *
        AddressPhaseConjugation.phaseDiagonal q *
        (BinaryAddressPermutation.matrix
          (ι := ι × Fin h) (lift (ι := ι) (denseSwap h hh heven)))⁻¹ =
      AddressPhaseConjugation.phaseDiagonal
        (q ∘ (fun x =>
          (BinaryAddressPermutation.induced
            (lift (ι := ι) (denseSwap h hh heven))).symm x)) := by
  exact AddressPhaseConjugation.matrix_conj_phaseDiagonal
    (lift (ι := ι) (denseSwap h hh heven)) q

/-- Binary transvection of the anchored coordinate gives the dense label. -/
theorem dense_transvection_coordinate {h : ℕ}
    (hh : 2 ≤ h) (heven : Even h) :
    transvection (allOnes (h := h))
        (coordinate (zeroIndex (by omega : 1 ≤ h))) =
      denseComplementLabel (h := h) (by omega : 1 ≤ h) := by
  rw [transvection_apply]
  have hone : dotProduct (allOnes (h := h))
      (coordinate (zeroIndex (by omega : 1 ≤ h))) = (1 : F2) := by
    simp [dotProduct, allOnes, coordinate, zeroIndex]
  rw [hone, one_smul]
  unfold denseComplementLabel unitLabel coordinate TripleSpan.basisVec
  exact add_comm _ _

/-- A single complex shear cannot globally realize the support-map image of
    the dense binary transvection.  This is only a support-encoding no-go; the
    paper's address-permutation semantics uses a different bridge. -/
theorem no_even_dense_shear_support_transport {h : ℕ}
    [NeZero h] (hh : 2 ≤ h) (heven : Even h) (s : Shear (Fin h)) :
    ¬ (∀ x : Active h,
      bitVectorToComplex
          (transvection (allOnes (h := h)) x) =
        s.act (bitVectorToComplex x)) := by
  intro htransport
  let w : Fin h := zeroIndex (by omega : 1 ≤ h)
  have hleft :
      bitVectorToComplex
          (transvection (allOnes (h := h)) (coordinate w)) w = 0 := by
    rw [dense_transvection_coordinate hh heven]
    change bitToComplex
      (denseComplementLabel (h := h) (by omega : 1 ≤ h) w) = 0
    rw [denseComplement_zero (h := h) (by omega : 1 ≤ h)]
    simp
  have hright : s.act (bitVectorToComplex (coordinate w)) w = 1 := by
    by_cases hi : w = s.i
    · have hjw : s.j ≠ w := by
        intro hj
        apply s.hij
        exact hi.symm.trans hj.symm
      simp [Shear.act, bitVectorToComplex, bitToComplex,
        coordinate, w, hi, hjw, s.hij]
    · simp [Shear.act, bitVectorToComplex, bitToComplex,
        coordinate, w, hi]
  have heq := congr_fun (htransport (coordinate w)) w
  rw [hleft, hright] at heq
  norm_num at heq

end DenseTwoFrameComplexBridge
end ExactFourier
end OAI
