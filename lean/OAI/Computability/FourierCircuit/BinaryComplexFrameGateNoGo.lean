import OAI.Computability.FourierCircuit.BinaryComplexFrameMap
import Mathlib.Tactic

/-!
# A concrete one-gate frame-transport obstruction

The support encoding from `ZMod 2` to `0/1 ⊂ ℂ` agrees with addition only when
supports are disjoint.  The smallest isotropic binary transvection is already
the swap direction `e₀ + e₁` on `Fin 2`: it exchanges the two coordinate labels.
A single complex `Gate.add` in the `0`-target/`1`-source orientation fixes
`e₀` and therefore cannot transport that binary transvection for every input.
This is a route-specific obstruction to identifying one directional binary
transvection with one scalar `Gate.add`; it is not a lower bound for arbitrary
complex circuits, which may use permutations or multiple shears.
-/

namespace OAI
namespace ExactFourier
namespace BinaryComplexFrameGateNoGo

open BinaryTransvection
open BinaryComplexFrameMap

abbrev H := 2
abbrev F2 := ZMod 2

noncomputable def swapDirection : Fin H → F2 :=
  coordinate 0 + coordinate 1

noncomputable def unitAddShear : Shear (Fin H) where
  i := 0
  j := 1
  hij := by decide
  c := 1

/-- The binary swap direction cannot be transported by one oriented unit add. -/
theorem unit_add_not_frame_transport :
    ¬ FrameToComplexShearPremise swapDirection unitAddShear := by
  intro h
  have hf := h.frame_transport (coordinate (0 : Fin H))
  have hj := congrFun hf (1 : Fin H)
  norm_num [swapDirection, unitAddShear, BinaryTransvection.transvection_apply,
    BinaryTransvection.dot_coordinate, BinaryComplexFrameMap.bitVectorToComplex,
    BinaryComplexFrameMap.bitToComplex, Shear.act, BinaryTransvection.coordinate]
    at hj

end BinaryComplexFrameGateNoGo
end ExactFourier
end OAI
