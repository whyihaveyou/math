import OAI.Computability.FourierCircuit.FrameLabels
import Mathlib.Tactic

/-!
# Local frame mismatch for complement moments

The complement moment `b_i` touches source triples avoiding `i`, while a
 target triple used to read it contains `i`.  At the indicator level the source
labels lie in the coordinate hyperplane `z_i = 0`, and the target label does
not.  This is a local nesting obstruction for the complement basis; it is not
a lower bound for arbitrary framed networks.
-/

namespace OAI
namespace ExactFourier
namespace ComplementMomentFrameMismatch

open FrameLabels

def coordinateKernel {h : ℕ} (i : Fin h) :
    Submodule (ZMod 2) (Fin h → ZMod 2) :=
  (LinearMap.proj i : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2).ker

theorem avoiding_indicator_mem_kernel {h : ℕ}
    (i : Fin h) (T : Finset (Fin h)) (hTi : i ∉ T) :
    indicator T ∈ coordinateKernel i := by
  rw [coordinateKernel, LinearMap.mem_ker]
  simp [indicator, hTi]

theorem containing_indicator_not_mem_kernel {h : ℕ}
    (i : Fin h) (S : Finset (Fin h)) (hiS : i ∈ S) :
    indicator S ∉ coordinateKernel i := by
  intro hmem
  rw [coordinateKernel, LinearMap.mem_ker] at hmem
  simp [indicator, hiS] at hmem

end ComplementMomentFrameMismatch
end ExactFourier
end OAI
