import OAI.Computability.FourierCircuit.CenterFramedInvocation
import OAI.Computability.FourierCircuit.PairComplementInvocation
import OAI.Computability.FourierCircuit.PairComplementFrameTransportCandidate

/-!
# Frame-labelled pair/complement invocation

`PairComplementInvocation` proves the exact h=24 scalar identity using both the
A and B pair banks and the direct diagonal bank.  This file binds that scalar
state to the existing prefix frame, so forward, inverse, and exchange carry a
single explicit source/target frame.  It is still a local certificate: the
physical complex gates, their commutation with the scalar maps, and a global
all-prefix schedule are not asserted here.
-/

namespace OAI
namespace ExactFourier
namespace PairComplementFramedInvocation

open CenterFramedInvocation
open PairComplementInvocation

abbrev F := ZMod 2
abbrev Source := PairComplementInvocation.Source
abbrev PairScalarState (K : Type*) :=
  CompressedInvocation.State (Source → K)
    (PairComplementInvocation.AggregateBank K) (Fin 24 → K)

variable {K : Type*} [Field K] [CharZero K]

structure FramedState where
  scalar : PairScalarState K
  frame : CenterFramedInvocation.PrefixFrame 24

noncomputable def forward (s : FramedState (K := K)) : FramedState (K := K) :=
  { scalar := CompressedInvocation.eightRows
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

noncomputable def inverse (s : FramedState (K := K)) : FramedState (K := K) :=
  { scalar := CompressedInvocation.inverseEightRows
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

noncomputable def exchange (s : FramedState (K := K)) : FramedState (K := K) :=
  { scalar := CompressedInvocation.threeInvocations
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

@[simp] theorem forward_frame (s : FramedState (K := K)) :
    (forward s).frame = s.frame := rfl

@[simp] theorem inverse_frame (s : FramedState (K := K)) :
    (inverse s).frame = s.frame := rfl

@[simp] theorem exchange_frame (s : FramedState (K := K)) :
    (exchange s).frame = s.frame := rfl

theorem forward_scalar_restore (s : FramedState (K := K)) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} := by
  exact PairComplementInvocation.forward_restore s.scalar

theorem inverse_scalar_restore (s : FramedState (K := K)) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} := by
  exact PairComplementInvocation.inverse_restore s.scalar

theorem exchange_scalar (s : FramedState (K := K)) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} := by
  exact PairComplementInvocation.three_exchange s.scalar

theorem forward_restore (s : FramedState (K := K)) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} ∧
      (forward s).frame = s.frame := by
  exact ⟨forward_scalar_restore s, forward_frame s⟩

theorem inverse_restore (s : FramedState (K := K)) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} ∧
      (inverse s).frame = s.frame := by
  exact ⟨inverse_scalar_restore s, inverse_frame s⟩

theorem exchange_restore (s : FramedState (K := K)) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} ∧
      (exchange s).frame = s.frame := by
  exact ⟨exchange_scalar s, exchange_frame s⟩

/-- Attach the audited first-prefix h=24 frame to an arbitrary pair scalar
state. -/
def h24 (s : PairScalarState K) : FramedState (K := K) :=
  { scalar := s, frame := h24PrefixFrame }

theorem h24_forward_restore (s : PairScalarState K) :
    (forward (h24 s)).scalar = {s with y := s.y + s.x} := by
  exact forward_scalar_restore (h24 s)

theorem h24_inverse_restore (s : PairScalarState K) :
    (inverse (h24 s)).scalar = {s with y := s.y - s.x} := by
  exact inverse_scalar_restore (h24 s)

theorem h24_exchange (s : PairScalarState K) :
    (exchange (h24 s)).scalar = {s with x := -s.y, y := s.x} := by
  exact exchange_scalar (h24 s)

end PairComplementFramedInvocation
end ExactFourier
end OAI
