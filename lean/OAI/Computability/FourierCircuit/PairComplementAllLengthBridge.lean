import OAI.Computability.FourierCircuit.PairComplementInvocation
import OAI.Computability.FourierCircuit.GlobalFrameTowerBridge
import OAI.Computability.FourierCircuit.CenterAllLengthBridge
import Mathlib.Tactic

/-!
# All-length attachment interface for the pair/complement invocation

`PairComplementInvocation` proves the scalar restoration law at `h = 24`,
while the tower files prove frame labels at every finite prefix depth.  The
two facts use different state types: the former was attached only to the
one-coordinate prefix `Fin 1`, whereas the latter uses
`TowerPrefix 24 k`.  This file supplies the smallest type-level bridge.

It attaches the pair/complement scalar state to an arbitrary finite prefix
whose active source and target labels are unit and orthogonal, and then
specializes that attachment to every stage of a `FrameTowerSchedule`.  The
forward, inverse, and exchange maps preserve the attached frame and satisfy
the exact scalar restoration laws.  No complex gate, bank-frame commutation,
or global physical schedule is asserted here; those remain explicit premises
for a circuit theorem.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace PairComplementAllLengthBridge

open CenterStageTowerTransport
open GlobalFrameTowerBridge
open GlobalFrameSchedule
open CenterAllLengthBridge
open PairComplementInvocation

abbrev F := ZMod 2
abbrev Active := Fin 24 → F

variable {K : Type*} [Field K] [CharZero K]

/-! ## A pair/complement frame at an arbitrary finite prefix -/

structure PairPrefixFrame (ι : Type*) [Fintype ι] [DecidableEq ι] where
  pre : ι → F
  source : Active
  target : Active
  prefix_unit : dotProduct pre pre = (1 : F)
  source_unit : dotProduct source source = (1 : F)
  target_unit : dotProduct target target = (1 : F)
  source_target_orthogonal : dotProduct source target = (0 : F)

namespace PairPrefixFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Address (ι : Type*) := ι × Fin 24 → F

def sourceLabel (f : PairPrefixFrame ι) : Address ι :=
  CenterRowGeneral.insert f.pre f.source

def targetLabel (f : PairPrefixFrame ι) : Address ι :=
  CenterRowGeneral.insert f.pre f.target

theorem sourceLabel_unit (f : PairPrefixFrame ι) :
    dotProduct f.sourceLabel f.sourceLabel = (1 : F) := by
  exact CenterRowGeneral.insert_dot_insert f.pre f.prefix_unit
    f.source f.source |>.trans f.source_unit

theorem targetLabel_unit (f : PairPrefixFrame ι) :
    dotProduct f.targetLabel f.targetLabel = (1 : F) := by
  exact CenterRowGeneral.insert_dot_insert f.pre f.prefix_unit
    f.target f.target |>.trans f.target_unit

theorem labels_orthogonal (f : PairPrefixFrame ι) :
    dotProduct f.sourceLabel f.targetLabel = (0 : F) := by
  exact CenterRowGeneral.insert_dot_insert f.pre f.prefix_unit
    f.source f.target |>.trans f.source_target_orthogonal

end PairPrefixFrame

/-! ## Scalar state attached to the arbitrary prefix frame -/

abbrev ScalarState := CompressedInvocation.State
  (PairComplementInvocation.Source → K)
  (PairComplementInvocation.AggregateBank K)
  (Fin 24 → K)

structure FramedState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  scalar : ScalarState (K := K)
  frame : PairPrefixFrame ι

noncomputable def forward
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : FramedState (K := K) ι :=
  { scalar := CompressedInvocation.eightRows
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

noncomputable def inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : FramedState (K := K) ι :=
  { scalar := CompressedInvocation.inverseEightRows
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

noncomputable def exchange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : FramedState (K := K) ι :=
  { scalar := CompressedInvocation.threeInvocations
      CompressedInvocation.OrderedPairs.RHom
      CenterCompression.compressedG
      PairComplementInvocation.aggregateReadHom
      PairComplementInvocation.aggregateInput s.scalar
    frame := s.frame }

@[simp] theorem forward_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : (forward s).frame = s.frame := rfl

@[simp] theorem inverse_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : (inverse s).frame = s.frame := rfl

@[simp] theorem exchange_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) : (exchange s).frame = s.frame := rfl

theorem forward_scalar_restore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} := by
  exact PairComplementInvocation.forward_restore s.scalar

theorem inverse_scalar_restore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} := by
  exact PairComplementInvocation.inverse_restore s.scalar

theorem exchange_scalar
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} := by
  exact PairComplementInvocation.three_exchange s.scalar

theorem forward_restore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (forward s).scalar = {s.scalar with y := s.scalar.y + s.scalar.x} ∧
      (forward s).frame = s.frame := by
  exact ⟨forward_scalar_restore s, forward_frame s⟩

theorem inverse_restore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (inverse s).scalar = {s.scalar with y := s.scalar.y - s.scalar.x} ∧
      (inverse s).frame = s.frame := by
  exact ⟨inverse_scalar_restore s, inverse_frame s⟩

theorem exchange_restore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : FramedState (K := K) ι) :
    (exchange s).scalar = {s.scalar with x := -s.scalar.y, y := s.scalar.x} ∧
      (exchange s).frame = s.frame := by
  exact ⟨exchange_scalar s, exchange_frame s⟩

/-! ## Attachment to the all-length tower -/

noncomputable def towerFrame
    (S : FrameTowerSchedule 24) (k : ℕ) :
    PairPrefixFrame (TowerPrefix 24 k) where
  pre := towerPrefix 24 S.p0 S.a k
  source := S.a k
  target := S.a (k + 1)
  prefix_unit := towerPrefix_unit 24 S.p0 S.a S.prefix_unit S.active_unit k
  source_unit := S.active_unit k
  target_unit := S.active_unit (k + 1)
  source_target_orthogonal := S.active_step_orthogonal k

theorem towerFrame_source_unit
    (S : FrameTowerSchedule 24) (k : ℕ) :
    dotProduct (towerFrame S k).sourceLabel
      (towerFrame S k).sourceLabel = (1 : F) := by
  exact PairPrefixFrame.sourceLabel_unit (towerFrame S k)

theorem towerFrame_labels_orthogonal
    (S : FrameTowerSchedule 24) (k : ℕ) :
    dotProduct (towerFrame S k).sourceLabel
      (towerFrame S k).targetLabel = (0 : F) := by
  exact PairPrefixFrame.labels_orthogonal (towerFrame S k)

theorem towerFrame_boundary_transport
    (S : FrameTowerSchedule 24) (k : ℕ) :
    tensorLift (S.a (k + 1)) (towerFrame S k).sourceLabel =
      (towerFrame S (k + 1)).sourceLabel := by
  unfold towerFrame PairPrefixFrame.sourceLabel
  exact towerTransition S.p0 S.a k

theorem tower_pair_forward_restore
    (S : FrameTowerSchedule 24) (k : ℕ)
    (s : ScalarState (K := K)) :
    (forward (ι := TowerPrefix 24 k)
      { scalar := s, frame := towerFrame S k }).scalar =
        {s with y := s.y + s.x} := by
  exact forward_scalar_restore _

theorem tower_pair_exchange_restore
    (S : FrameTowerSchedule 24) (k : ℕ)
    (s : ScalarState (K := K)) :
    (exchange (ι := TowerPrefix 24 k)
      { scalar := s, frame := towerFrame S k }).scalar =
        {s with x := -s.y, y := s.x} := by
  exact exchange_scalar _

/-! The remaining physical obligations are intentionally explicit. -/

structure PhysicalPairBridgePremise (h : ℕ) where
  scalar_commutes_with_frame : Prop
  bank_transport : Prop
  global_schedule : Prop

theorem tower_attachment_is_not_physical
    (S : FrameTowerSchedule 24) (k : ℕ)
    (s : ScalarState (K := K)) :
    (forward (ι := TowerPrefix 24 k)
      { scalar := s, frame := towerFrame S k }).frame =
        towerFrame S k := by
  rfl

end PairComplementAllLengthBridge
end ExactFourier
end OAI
