import OAI.Computability.FourierCircuit.SideMomentRedundantGlobalAudit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace SharedIncidenceFactorization

open CenterCompression
open SideMomentFactorization
open SideMomentRedundantGlobalAudit

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

/-- The common incidence feature map used by both the compressed centre and the
q-free side moment.  It records, for every coordinate `i`, the sum of source
triple coefficients whose label contains `i`. -/
def incidenceA (x : Triple h → K) : Fin h → K :=
  fun i => sideMoment1 x i

/-- The incidence feature map as a linear map. -/
def incidenceHom : (Triple h → K) →ₗ[K] (Fin h → K) where
  toFun := incidenceA
  map_add' := by
    classical
    intro x y
    funext i
    unfold incidenceA sideMoment1
    change (∑ T ∈ (tripleSet h).attach,
      if i ∈ T.1 then x T + y T else 0) =
      (∑ T ∈ (tripleSet h).attach,
        if i ∈ T.1 then x T else 0) +
      (∑ T ∈ (tripleSet h).attach,
        if i ∈ T.1 then y T else 0)
    have hterm :
        (∑ T ∈ (tripleSet h).attach,
          if i ∈ T.1 then x T + y T else 0) =
          ∑ T ∈ (tripleSet h).attach,
            ((if i ∈ T.1 then x T else 0) +
              (if i ∈ T.1 then y T else 0)) := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hit : i ∈ T.1 <;> simp [hit]
    rw [hterm, Finset.sum_add_distrib]
  map_smul' := by
    classical
    intro a x
    funext i
    unfold incidenceA sideMoment1
    change (∑ T ∈ (tripleSet h).attach,
      if i ∈ T.1 then a * x T else 0) =
      a * (∑ T ∈ (tripleSet h).attach,
        if i ∈ T.1 then x T else 0)
    have hterm :
        (∑ T ∈ (tripleSet h).attach,
          if i ∈ T.1 then a * x T else 0) =
          ∑ T ∈ (tripleSet h).attach,
            a * (if i ∈ T.1 then x T else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hit : i ∈ T.1 <;> simp [hit]
    rw [hterm, Finset.mul_sum]

/-- Read out the compressed centre coordinates from the incidence features. -/
def centerReadoutA : (Fin h → K) →ₗ[K] (Fin h → K) where
  toFun := fun a i => a i - (∑ j : Fin h, a j) / (9 : K)
  map_add' := by
    intro a b
    funext i
    change (a i + b i - (∑ j : Fin h, (a j + b j)) / (9 : K)) =
      (a i - (∑ j : Fin h, a j) / (9 : K)) +
        (b i - (∑ j : Fin h, b j) / (9 : K))
    rw [Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c a
    funext i
    change (c * a i - (∑ j : Fin h, c * a j) / (9 : K)) =
      c * (a i - (∑ j : Fin h, a j) / (9 : K))
    rw [← Finset.mul_sum]
    ring

/-- Read out the q-free side correction from the same incidence features. -/
def sideReadoutA : (Fin h → K) →ₗ[K] (Triple h → K) where
  toFun := fun a S =>
    ((∑ i : Fin h, a i) / (3 : K) - ∑ i ∈ S.1, a i) / (2 : K)
  map_add' := by
    intro a b
    funext S
    change (((∑ i : Fin h, (a i + b i)) / (3 : K) -
      (∑ i ∈ S.1, (a i + b i))) / (2 : K)) =
      (((∑ i : Fin h, a i) / (3 : K) - ∑ i ∈ S.1, a i) / (2 : K)) +
      (((∑ i : Fin h, b i) / (3 : K) - ∑ i ∈ S.1, b i) / (2 : K))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c a
    funext S
    change (((∑ i : Fin h, c * a i) / (3 : K) -
      (∑ i ∈ S.1, c * a i)) / (2 : K)) =
      c * (((∑ i : Fin h, a i) / (3 : K) - ∑ i ∈ S.1, a i) / (2 : K))
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring

/-- The incidence total is exactly three times the global source sum. -/
theorem incidenceA_total_eq_three_mul_global (x : Triple h → K) :
    (∑ i : Fin h, incidenceA x i) = 3 * sideMoment0 x := by
  simpa [incidenceA, SideMomentRedundantGlobalAudit.incidenceTotal,
    SideMomentFactorization.sideMoment0] using
    (SideMomentRedundantGlobalAudit.incidenceTotal_eq_three_mul_global
      (h := h) (K := K) x)

/-- The centre map factors through the common incidence map. -/
theorem compressedG_factor_through_incidence (x : Triple h → K) :
    compressedG (K := K) x = centerReadoutA (incidenceA x) := by
  funext i
  unfold compressedG centerReadoutA incidenceA
  change (∑ T ∈ (tripleSet h).attach,
      if i ∈ T.1 then x T else 0) -
      (∑ T ∈ (tripleSet h).attach, x T) / (3 : K) =
    sideMoment1 x i - (∑ j : Fin h, sideMoment1 x j) / (9 : K)
  have htotal :
      (∑ i : Fin h, sideMoment1 x i) =
        3 * (∑ T ∈ (tripleSet h).attach, x T) := by
    simpa [SideMomentRedundantGlobalAudit.incidenceTotal,
      SideMomentFactorization.sideMoment0] using
      (SideMomentRedundantGlobalAudit.incidenceTotal_eq_three_mul_global
        (h := h) (K := K) x)
  rw [htotal]
  unfold sideMoment1
  ring

/-- The q-free side map factors through the common incidence map. -/
theorem sideMomentNoGlobal_factor_through_incidence
    (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobal S x = sideReadoutA (incidenceA x) S := by
  unfold sideMomentNoGlobal sideReadoutA incidenceA
  change ((1 / (3 : K)) * incidenceTotal x -
    (∑ i ∈ S.1, sideMoment1 x i)) / (2 : K) =
      ((∑ i : Fin h, sideMoment1 x i) / (3 : K) -
        (∑ i ∈ S.1, sideMoment1 x i)) / (2 : K)
  unfold incidenceTotal
  ring

/-- The two linear maps are explicitly the same incidence factorization. -/
def compressedGHom : (Triple h → K) →ₗ[K] (Fin h → K) :=
  centerReadoutA.comp incidenceHom

def sideMomentNoGlobalHom : (Triple h → K) →ₗ[K] (Triple h → K) :=
  sideReadoutA.comp incidenceHom

theorem compressedGHom_apply (x : Triple h → K) :
    compressedGHom (K := K) x = compressedG (K := K) x := by
  symm
  exact compressedG_factor_through_incidence x

theorem sideMomentNoGlobalHom_apply (S : Triple h) (x : Triple h → K) :
    sideMomentNoGlobalHom (K := K) x S = sideMomentNoGlobal S x := by
  symm
  exact sideMomentNoGlobal_factor_through_incidence S x

/-- Every incidence feature vector lies in an `h`-dimensional codomain, so its
linear range has finrank at most `h`.  This is a rank certificate for both
factorized readouts; it is algebraic and does not assert a physical circuit
schedule. -/
theorem incidence_range_finrank_le :
    Module.finrank K (LinearMap.range (incidenceHom (h := h) (K := K))) ≤ h := by
  have hr :
      Module.finrank K (LinearMap.range (incidenceHom (h := h) (K := K))) ≤
        Module.finrank K (Fin h → K) :=
    (LinearMap.range (incidenceHom (h := h) (K := K))).finrank_le
  simpa using hr

/-- The centre readout cannot increase the feature rank. -/
theorem compressedG_range_finrank_le :
    Module.finrank K (LinearMap.range (compressedGHom (h := h) (K := K))) ≤ h := by
  have hcomp :
      LinearMap.rank (compressedGHom (h := h) (K := K)) ≤
        LinearMap.rank (incidenceHom (h := h) (K := K)) := by
    exact LinearMap.rank_comp_le_right _ _
  have hfin :
      Module.finrank K (LinearMap.range (compressedGHom (h := h) (K := K))) ≤
        Module.finrank K (LinearMap.range (incidenceHom (h := h) (K := K))) := by
    apply Module.finrank_le_finrank_of_rank_le_rank
    · exact Cardinal.lift_le.mpr hcomp
    · exact Module.rank_lt_aleph0 K
        (LinearMap.range (incidenceHom (h := h) (K := K)))
  exact hfin.trans (incidence_range_finrank_le (h := h) (K := K))

/-- The q-free side readout cannot increase the feature rank. -/
theorem sideMomentNoGlobal_range_finrank_le :
    Module.finrank K (LinearMap.range
      (sideMomentNoGlobalHom (h := h) (K := K))) ≤ h := by
  have hcomp :
      LinearMap.rank (sideMomentNoGlobalHom (h := h) (K := K)) ≤
        LinearMap.rank (incidenceHom (h := h) (K := K)) := by
    exact LinearMap.rank_comp_le_right _ _
  have hfin :
      Module.finrank K (LinearMap.range
          (sideMomentNoGlobalHom (h := h) (K := K))) ≤
        Module.finrank K (LinearMap.range (incidenceHom (h := h) (K := K))) := by
    apply Module.finrank_le_finrank_of_rank_le_rank
    · exact Cardinal.lift_le.mpr hcomp
    · exact Module.rank_lt_aleph0 K
        (LinearMap.range (incidenceHom (h := h) (K := K)))
  exact hfin.trans (incidence_range_finrank_le (h := h) (K := K))

/-- The pair of outputs can be emitted together without increasing the feature
rank: it still factors through the same incidence vector. -/
def jointReadoutA :
    (Fin h → K) →ₗ[K] ((Fin h → K) × (Triple h → K)) :=
  centerReadoutA.prod sideReadoutA

def jointIncidenceHom :
    (Triple h → K) →ₗ[K] ((Fin h → K) × (Triple h → K)) :=
  jointReadoutA.comp incidenceHom

theorem jointIncidence_range_finrank_le :
    Module.finrank K (LinearMap.range
      (jointIncidenceHom (h := h) (K := K))) ≤ h := by
  have hcomp :
      LinearMap.rank (jointIncidenceHom (h := h) (K := K)) ≤
        LinearMap.rank (incidenceHom (h := h) (K := K)) := by
    exact LinearMap.rank_comp_le_right _ _
  have hfin :
      Module.finrank K (LinearMap.range
          (jointIncidenceHom (h := h) (K := K))) ≤
        Module.finrank K (LinearMap.range (incidenceHom (h := h) (K := K))) := by
    apply Module.finrank_le_finrank_of_rank_le_rank
    · exact Cardinal.lift_le.mpr hcomp
    · exact Module.rank_lt_aleph0 K
        (LinearMap.range (incidenceHom (h := h) (K := K)))
  exact hfin.trans (incidence_range_finrank_le (h := h) (K := K))

/-- Concrete h = 24 instance of the common-incidence rank certificate. -/
theorem incidence_range_finrank_le_h24 :
    Module.finrank K
        (LinearMap.range (incidenceHom (h := 24) (K := K))) ≤ 24 := by
  simpa using (incidence_range_finrank_le (h := 24) (K := K))

end SharedIncidenceFactorization
end ExactFourier
end OAI
