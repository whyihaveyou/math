import OAI.Computability.FourierCircuit.CenterCompression
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The minimal cubic correction is the diagonal

Pair/complement and centre moments give the quadratic coefficient
`(1-r)/2`, where `r = |S ∩ T|`.  On triples this takes values
`(1/2,0,-1/2,-1)` for `r=0,1,2,3`.  The desired side coefficient is zero at
`r=3`, so the unique missing cubic term is `choose r 3`, which is exactly the
identity matrix on triples.  Any linear bank carrying this correction has
full source rank 2024.  The final arithmetic records the existing common-frame
charge as a conditional cost; no universal network lower bound is claimed.
-/

namespace OAI
namespace ExactFourier
namespace PairCubicDiagonalNoGo

def quadratic (r : Fin 4) : ℚ := (1 - (r.val : ℚ)) / 2

def side (r : Fin 4) : ℚ :=
  if r.val = 0 then 1 / 2 else
  if r.val = 1 then 0 else
  if r.val = 2 then -1 / 2 else 0

def diagonal (r : Fin 4) : ℚ := (Nat.choose r.val 3 : ℚ)

theorem side_eq_quadratic_add_diagonal (r : Fin 4) :
    side r = quadratic r + diagonal r := by
  fin_cases r <;> norm_num [side, quadratic, diagonal, Nat.choose]

theorem diagonal_values :
    diagonal 0 = 0 ∧ diagonal 1 = 0 ∧ diagonal 2 = 0 ∧ diagonal 3 = 1 := by
  norm_num [diagonal, Nat.choose]

/- Any (possibly non-symmetric) linear factorization of the identity must have
   an auxiliary space at least as large as the source.  This is the exact
   rank statement used for the cubic diagonal correction. -/
theorem identity_factorization_finrank_lower_bound
    {K X R : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup R] [Module K R] [FiniteDimensional K X]
    [FiniteDimensional K R]
    (U : R →ₗ[K] X) (V : X →ₗ[K] R)
    (hUV : (U.comp V) = LinearMap.id) :
    Module.finrank K X ≤ Module.finrank K R := by
  apply LinearMap.finrank_le_finrank_of_injective
  intro x y hxy
  have hx : U (V x) = x := by
    have h := congrArg (fun f : X →ₗ[K] X => f x) hUV
    simpa using h
  have hy : U (V y) = y := by
    have h := congrArg (fun f : X →ₗ[K] X => f y) hUV
    simpa using h
  calc
    x = U (V x) := hx.symm
    _ = U (V y) := by rw [hxy]
    _ = y := hy

namespace H24

open CenterCompression

def h : ℕ := CenterCompression.H24.h
def v : ℕ := CenterCompression.H24.v
def N0 : ℕ := CenterCompression.H24.N0
def I0 : ℕ := CenterCompression.H24.I0
def m : ℕ := CenterCompression.H24.m

/- A full-rank cubic/diagonal bank replaces the direct source bank. -/
def cubicRoleCount : ℕ := 2 * N0 + I0 * (v + h)
def padding : ℕ := 2 ^ 36
def saving : ℕ := CenterCompression.H24.deltaCompressed
def framePenalty : ℕ := 2 * I0 * v
def margin : ℤ := (saving : ℤ) - (framePenalty : ℤ)

theorem cubicRoleCount_eq : cubicRoleCount = 41752302592 := by
  norm_num [cubicRoleCount, N0, I0, v, h,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem padding_eq : padding = 68719476736 := by norm_num [padding]

theorem padding_bounds : 2 ^ 35 < cubicRoleCount ∧ cubicRoleCount ≤ padding := by
  norm_num [cubicRoleCount, N0, I0, v, h, padding,
    CenterCompression.H24.N0, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem framePenalty_eq : framePenalty = 49748818944 := by
  norm_num [framePenalty, I0, v, CenterCompression.H24.I0,
    CenterCompression.H24.v, CenterCompression.H24.h, Nat.choose]

theorem saving_eq : saving = 2425172992 := by
  exact CenterCompression.H24.deltaCompressed_eq

theorem margin_eq : margin = -47323645952 := by
  norm_num [margin, saving_eq, framePenalty_eq]

theorem margin_negative : margin < 0 := by
  rw [margin_eq]
  norm_num

end H24
end PairCubicDiagonalNoGo
end ExactFourier
end OAI
