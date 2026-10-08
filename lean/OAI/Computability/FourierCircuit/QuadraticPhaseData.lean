import OAI.Computability.FourierCircuit.AddressPhaseConjugation

/-!
# Explicit data for a projected quadratic phase

`AddressPhaseConjugation` proves the conjugation theorem for an arbitrary
complex profile `q`.  This file packages the additional data needed for the
paper's proposed profile

```text
q_U x = Complex.I ^ (weight (P_U x)).
```

The structure is intentionally only a data interface.  It does not claim that
the supplied frame is Walsh, that `weight` is a Hamming weight, or that the
resulting profile satisfies a quadratic identity.  Those properties remain
separate proof obligations for a concrete construction.
-/

namespace OAI
namespace ExactFourier
namespace AddressPhaseConjugation

open BinaryAddressPermutation

/-!
`U` is the selected address subspace.  `projection_mem` and `projection_fixed`
are the minimum explicit facts that make `projection` a retraction onto `U`;
surjectivity onto all of `U` can be added by a future concrete instance when
needed.  `q` is retained as a field so that a construction may use a different
normalization while proving `q_eq` separately.
-/
structure QuadraticPhaseData (ι : Type) [Fintype ι] [DecidableEq ι] where
  U : Submodule F2 (Address ι)
  projection : Address ι →ₗ[F2] Address ι
  projection_mem : ∀ x, projection x ∈ U
  projection_fixed : ∀ ⦃u : Address ι⦄, u ∈ U → projection u = u
  weight : Address ι → ℕ
  q : Address ι → ℂ
  q_eq : ∀ x, q x = Complex.I ^ weight (projection x)

/-- The phase profile determined by the projection and weight fields. -/
noncomputable def QuadraticPhaseData.qU
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι) : Address ι → ℂ :=
  fun x => Complex.I ^ data.weight (data.projection x)

theorem QuadraticPhaseData.q_eq_qU
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι) : data.q = data.qU := by
  funext x
  exact data.q_eq x

/-!
The generic phase theorem can now be instantiated with the supplied profile.
The only frame hypothesis is the same explicit commutation relation required
by `matrix_conj_framedPhase_of_commutes`; no Walsh property is inferred.
-/
theorem QuadraticPhaseData.conj_framedPhase
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι)
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (hJ : matrix e * J = J * matrix e) :
    matrix e * framedPhase J data.q * (matrix e)⁻¹ =
      framedPhase J (data.q ∘ (fun x => (induced e).symm x)) := by
  exact matrix_conj_framedPhase_of_commutes e J data.q hJ

/-- The same conjugation statement with the explicit `q_U` expression. -/
theorem QuadraticPhaseData.conj_qU_framedPhase
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι)
    (e : Address ι ≃ₗ[F2] Address ι)
    (J : Matrix (Address ι) (Address ι) ℂ)
    (hJ : matrix e * J = J * matrix e) :
    matrix e * framedPhase J data.qU * (matrix e)⁻¹ =
      framedPhase J (data.qU ∘ (fun x => (induced e).symm x)) := by
  rw [← data.q_eq_qU]
  exact data.conj_framedPhase e J hJ

/-- Weight invariance under the induced address relabelling makes the explicit
`q_U` profile invariant.  This is the exact hypothesis a concrete projected
quadratic phase must discharge before using the diagonal commutation theorem.
-/
theorem QuadraticPhaseData.qU_comp_induced_symm_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι)
    (e : Address ι ≃ₗ[F2] Address ι)
    (hweight : ∀ x,
      data.weight (data.projection ((induced e).symm x)) =
        data.weight (data.projection x)) :
    data.qU ∘ (fun x => (induced e).symm x) = data.qU := by
  funext x
  simp only [Function.comp_apply, QuadraticPhaseData.qU]
  rw [hweight x]

/-- The preceding profile invariance is sufficient for phase-diagonal
commutation; no Walsh property is inferred from it. -/
theorem QuadraticPhaseData.commutes_phaseDiagonal_qU
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : QuadraticPhaseData ι)
    (e : Address ι ≃ₗ[F2] Address ι)
    (hweight : ∀ x,
      data.weight (data.projection ((induced e).symm x)) =
        data.weight (data.projection x)) :
    matrix e * phaseDiagonal data.qU = phaseDiagonal data.qU * matrix e := by
  exact matrix_commutes_phaseDiagonal e data.qU
    (data.qU_comp_induced_symm_eq e hweight)

end AddressPhaseConjugation
end ExactFourier
end OAI
