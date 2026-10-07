import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic

/-!
# Projection obstruction for a zero-trace side residual

The published source-indexed side map has no diagonal coefficients, hence
zero trace.  If the centre composite `P = RG` were a projection, then the
required residual `1 - P` would be idempotent.  In characteristic zero, a
zero-trace idempotent is zero, so `P` must be the whole identity.  In
particular, a proper rank-h projection cannot retain the published side
support.  This file states the trace premise explicitly; it does not prove a
new network support theorem or cover an arbitrary redesigned side update.
-/

namespace OAI.ExactFourier.ProjectionSideTraceObstruction

variable {K X : Type*} [Field K] [CharZero K]
variable [AddCommGroup X] [Module K X] [FiniteDimensional K X]

theorem projection_eq_one_of_residual_trace_zero
    (P : X →ₗ[K] X) (hP : IsIdempotentElem P)
    (htrace : LinearMap.trace K X (1 - P) = 0) : P = 1 := by
  have hzero : (1 - P : X →ₗ[K] X) = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hP.one_sub htrace
  exact (sub_eq_zero.mp hzero).symm

theorem proper_projection_residual_trace_ne_zero
    (P : X →ₗ[K] X) (hP : IsIdempotentElem P) (hproper : P ≠ 1) :
    LinearMap.trace K X (1 - P) ≠ 0 := by
  intro htrace
  exact hproper (projection_eq_one_of_residual_trace_zero P hP htrace)

/-- This form applies directly to an equality `P + side = 1`. -/
theorem projection_eq_one_of_zero_trace_side
    (P side : X →ₗ[K] X) (hP : IsIdempotentElem P)
    (hidentity : P + side = 1) (htrace : LinearMap.trace K X side = 0) :
    P = 1 := by
  apply projection_eq_one_of_residual_trace_zero P hP
  have hside : side = 1 - P := by
    rw [← hidentity]
    abel
  rw [← hside]
  exact htrace

end OAI.ExactFourier.ProjectionSideTraceObstruction
