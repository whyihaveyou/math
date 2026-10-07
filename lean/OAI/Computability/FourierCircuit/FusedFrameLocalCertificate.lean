import OAI.Computability.FourierCircuit.CenterFramedInvocation
import OAI.Computability.FourierCircuit.FusedCentreInvocation
import OAI.Computability.FourierCircuit.CenterBoundaryTensorProjection

/-!
# Local certificate for a fused, frame-labelled centre readout

This file joins three already separate interfaces:

* `CenterFramedInvocation` supplies a source and target active label carried by
  a fixed prefix frame;
* `FusedCentreInvocation` proves, over an arbitrary field, that the fused six
  row scalar map restores both auxiliary banks and sends `y` to `y + x`;
* `CenterBoundaryTensorProjection` proves that a source-row contribution plus
  the lifted sheared target line belongs to the old target boundary.

`FusedFrameLocalCertificate` packages the data needed for this local join.  Its
`valid` theorem is deliberately a conjunction of a scalar statement and a
binary-label submodule statement.  It does **not** assert that the binary
transvection is one legal complex gate, that the scalar map commutes with that
gate, or that certificates for all prefixes can be placed in one global DAG.
Those gate and global-schedule facts remain premises for any physical circuit
theorem.
-/

namespace OAI
namespace ExactFourier
namespace FusedFrameLocalCertificate

open CenterFramedInvocation
open FusedCentreInvocation
open CompressedInvocation
open CenterBoundaryTensorLift
open CenterBoundaryTensorProjection
open CenterBoundaryShearCandidate
open SideRowGeneralArbitrary
open BinaryTransvection

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev Address (ι : Type*) (h : ℕ) := ι × Fin h → F

variable {ι : Type*} [Fintype ι]
variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

/-! ## The local data

The source and target labels are read from `framed.frame`; this is the small
frame-compatibility condition that prevents a free-standing boundary witness
from being mistaken for the label carried by the scalar invocation.  The
prefix may have any finite type `ι`, since the tensor-projection theorem is
fibrewise and does not require `ι = Fin 1`.
-/

structure Data where
  framed : CenterFramedInvocation.FramedState h K
  pre : ι → F
  pre_unit : dotProduct pre pre = (1 : F)
  witness : Fin h
  witness_zero : framed.frame.target witness = 0
  source_row : Address ι h
  source_row_mem : source_row ∈
    SideRowGeneralArbitrary.L2 pre framed.frame.source

/-! A fused scalar forward map which retains the frame label. -/

noncomputable def fusedForward (s : CenterFramedInvocation.FramedState h K) :
    CenterFramedInvocation.FramedState h K :=
  { scalar := FusedCentreInvocation.fusedRows
      OrderedPairs.RHom CenterCompression.compressedG
      OrderedPairs.JHom OrderedPairs.V s.scalar
    frame := s.frame }

@[simp] theorem fusedForward_frame
    (s : CenterFramedInvocation.FramedState h K) :
    (fusedForward s).frame = s.frame := rfl

theorem fusedForward_scalar_update
    (s : CenterFramedInvocation.FramedState h K) :
    (fusedForward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} := by
  exact FusedCentreInvocation.OrderedPairs.compressed_fused_restore s.scalar

/-! ## The combined local result -/

theorem lifted_readout_legal (d : Data (ι := ι) (h := h) (K := K)) :
    d.source_row +
        CenterBoundaryTensorLift.lift
          (unitCoordinateEquiv d.framed.frame.target d.witness
            d.framed.frame.target_unit d.witness_zero)
          (CenterRowGeneral.insert d.pre d.framed.frame.target) ∈
      SideRowGeneralArbitrary.L5 d.pre d.framed.frame.target := by
  exact CenterBoundaryTensorProjection.lifted_sheared_readout_mem_L5
    d.pre d.framed.frame.source d.framed.frame.target
    d.pre_unit d.framed.frame.target_unit
    d.framed.frame.source_target_orthogonal d.witness d.witness_zero
    d.source_row d.source_row_mem

/-- The scalar fused update and the lifted frame-compatible readout hold at
    the same fixed prefix.  This is a local certificate only: gate semantics,
    scalar/gate commutation, and a global all-prefix schedule are deliberately
    absent and must be supplied by a later physical-circuit theorem. -/
theorem valid (d : Data (ι := ι) (h := h) (K := K)) :
    (fusedForward d.framed).scalar =
        {d.framed.scalar with y := d.framed.scalar.y + d.framed.scalar.x} ∧
      d.source_row +
          CenterBoundaryTensorLift.lift
            (unitCoordinateEquiv d.framed.frame.target d.witness
              d.framed.frame.target_unit d.witness_zero)
            (CenterRowGeneral.insert d.pre d.framed.frame.target) ∈
        SideRowGeneralArbitrary.L5 d.pre d.framed.frame.target := by
  exact ⟨fusedForward_scalar_update d.framed, lifted_readout_legal d⟩

/- The frame label is preserved by the fused scalar map.  Keeping this as a
   separate conjunct makes the local certificate usable by a later schedule
   proof without implying that such a schedule already exists. -/
theorem valid_with_frame (d : Data (ι := ι) (h := h) (K := K)) :
    (fusedForward d.framed).scalar =
        {d.framed.scalar with y := d.framed.scalar.y + d.framed.scalar.x} ∧
      (fusedForward d.framed).frame = d.framed.frame ∧
      d.source_row +
          CenterBoundaryTensorLift.lift
            (unitCoordinateEquiv d.framed.frame.target d.witness
              d.framed.frame.target_unit d.witness_zero)
            (CenterRowGeneral.insert d.pre d.framed.frame.target) ∈
        SideRowGeneralArbitrary.L5 d.pre d.framed.frame.target := by
  exact ⟨fusedForward_scalar_update d.framed,
    fusedForward_frame d.framed, lifted_readout_legal d⟩

/-! The concrete first-prefix object is useful to callers: an arbitrary scalar
state can be paired with the audited h=24 frame, while the prefix/readout data
remain explicit hypotheses rather than hidden global circuit claims. -/

def h24Data
    (s : CenterFramedInvocation.ScalarState 24 K)
    {ι : Type*} [Fintype ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (w : Fin 24) (hw : h24PrefixFrame.target w = 0)
    (z : Address ι 24)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p h24PrefixFrame.source) :
    Data (ι := ι) (h := 24) (K := K) :=
  { framed := CenterFramedInvocation.h24 s
    pre := p
    pre_unit := hp
    witness := w
    witness_zero := hw
    source_row := z
    source_row_mem := hz }

theorem h24_valid
    (s : CenterFramedInvocation.ScalarState 24 K)
    {ι : Type*} [Fintype ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (w : Fin 24) (hw : h24PrefixFrame.target w = 0)
    (z : Address ι 24)
    (hz : z ∈ SideRowGeneralArbitrary.L2 p h24PrefixFrame.source) :
    (fusedForward (CenterFramedInvocation.h24 s)).scalar =
        {s with y := s.y + s.x} ∧
      z +
          CenterBoundaryTensorLift.lift
            (unitCoordinateEquiv h24PrefixFrame.target w
              h24PrefixFrame.target_unit hw)
            (CenterRowGeneral.insert p h24PrefixFrame.target) ∈
        SideRowGeneralArbitrary.L5 p h24PrefixFrame.target := by
  simpa [h24Data, CenterFramedInvocation.h24] using
    (valid (h24Data (K := K) s p hp w hw z hz))

end FusedFrameLocalCertificate
end ExactFourier
end OAI
