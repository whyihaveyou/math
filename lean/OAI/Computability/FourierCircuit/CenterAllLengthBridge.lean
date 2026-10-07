import OAI.Computability.FourierCircuit.GlobalFrameTowerBridge

/-!
# Minimal all-length bridge for the centre-compressed frame schedule

`GlobalFrameTowerBridge` supplies a frame-labelled stage at every finite
address depth and proves the tensor-lift transport between consecutive
prefixes.  This file packages exactly the remaining bookkeeping that can be
proved without choosing a physical gate sequence: each invocation carries its
source/target labels and its centre/side directional-step counts, consecutive
invocations are joined by the finite tower lift, and the totals over any finite
prefix are additive.

The package is intentionally weaker than an all-length Fourier circuit.  It
does not define a gate, a circuit matrix, or a cost for the tensor lift.  Those
are explicit extra hypotheses for a future circuit theorem.
-/

namespace OAI
namespace ExactFourier
namespace CenterAllLengthBridge

open GlobalFrameSchedule
open GlobalFrameTowerBridge
open CenterStageTowerTransport
open StagePrefixLabelAudit

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F
abbrev FullAddress (h k : ℕ) := Fin (h ^ k) × Fin h → F

/-- One frame-labelled invocation at a fixed finite address depth.

The two labels are tied to the stage's actual prefix and active directions.
`centreSteps` and `sideSteps` are explicit bookkeeping fields: an eventual
physical implementation must provide them, while the recursive tower only
proves their audited values.
-/
structure FrameLabelledInvocation (h k : ℕ) where
  stage : GeneralStageFrame (Fin (h ^ k)) h
  sourceLabel : FullAddress h k
  targetLabel : FullAddress h k
  source_label_eq : sourceLabel = embeddedLabel stage.pre stage.source
  target_label_eq : targetLabel = embeddedLabel stage.pre stage.target
  centreSteps : ℕ
  sideSteps : ℕ
  centre_steps_eq : centreSteps = centreCount stage
  side_steps_eq : sideSteps = sideCount stage

def FrameLabelledInvocation.directionSteps {h k : ℕ}
    (v : FrameLabelledInvocation h k) : ℕ :=
  v.centreSteps + v.sideSteps

/-- A finite tower schedule records only the unit/orthogonality data needed by
    the algebraic frame transport. -/
structure FrameTowerSchedule (h : ℕ) where
  p0 : PrefixLabel h 0
  a : ℕ → Active h
  prefix_unit : dotProduct p0 p0 = (1 : F)
  active_unit : ∀ k, dotProduct (a k) (a k) = (1 : F)
  active_step_orthogonal : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F)

/-- The canonical frame-labelled invocation generated at depth `k`. -/
noncomputable def FrameTowerSchedule.invocation {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    FrameLabelledInvocation h k where
  stage := reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
    S.active_step_orthogonal k
  sourceLabel := embeddedLabel
    (reindexedPrefix S.p0 S.a k) (S.a k)
  targetLabel := embeddedLabel
    (reindexedPrefix S.p0 S.a k) (S.a (k + 1))
  source_label_eq := rfl
  target_label_eq := rfl
  centreSteps := centreCount
    (reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
      S.active_step_orthogonal k)
  sideSteps := sideCount
    (reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
      S.active_step_orthogonal k)
  centre_steps_eq := rfl
  side_steps_eq := rfl

@[simp] theorem FrameTowerSchedule.invocation_centre_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    (S.invocation hh k).centreSteps = h := by
  change centreCount
      (reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
        S.active_step_orthogonal k) = h
  exact (reindexedStage_counts hh S.p0 S.a S.prefix_unit S.active_unit
    S.active_step_orthogonal k).1

@[simp] theorem FrameTowerSchedule.invocation_side_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    (S.invocation hh k).sideSteps = h - 2 := by
  change sideCount
      (reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
        S.active_step_orthogonal k) = h - 2
  exact (reindexedStage_counts hh S.p0 S.a S.prefix_unit S.active_unit
    S.active_step_orthogonal k).2

/-- The exact directional-step count for one recursive invocation. -/
theorem FrameTowerSchedule.invocation_direction_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    (S.invocation hh k).directionSteps = 2 * h - 2 := by
  rw [FrameLabelledInvocation.directionSteps,
    S.invocation_centre_steps hh k, S.invocation_side_steps hh k]
  omega

/-- The source label is a unit vector and the source/target pair is
    orthogonal at every finite depth. -/
theorem FrameTowerSchedule.invocation_labels {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    dotProduct (S.invocation hh k).sourceLabel
        (S.invocation hh k).sourceLabel = (1 : F) ∧
      dotProduct (S.invocation hh k).sourceLabel
        (S.invocation hh k).targetLabel = (0 : F) := by
  let I := S.invocation hh k
  constructor
  · rw [I.source_label_eq]
    exact (reindexedStage hh S.p0 S.a S.prefix_unit S.active_unit
      S.active_step_orthogonal k).source_embedded_unit
  · rw [I.source_label_eq, I.target_label_eq]
    exact (reindexed_stage_interface hh S.p0 S.a S.prefix_unit
      S.active_unit S.active_step_orthogonal k).2.2.1

/-- The tower lift joins the source label of depth `k` to the source label of
    depth `k+1`.  This is the precise frame transition available before gate
    semantics are supplied. -/
theorem FrameTowerSchedule.invocation_boundary_transport {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    finTowerLift (S.a (k + 1))
        (S.invocation hh k).sourceLabel =
      (S.invocation hh (k + 1)).sourceLabel := by
  change finTowerLift (S.a (k + 1))
      (embeddedLabel (reindexedPrefix S.p0 S.a k) (S.a k)) =
    embeddedLabel (reindexedPrefix S.p0 S.a (k + 1)) (S.a (k + 1))
  exact finTowerLift_source S.p0 S.a k

/-- The target label at depth `k` is the same active label that starts the next
    step; only the prefix grows, via `invocation_boundary_transport`. -/
theorem FrameTowerSchedule.invocation_target_is_next_active {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (k : ℕ) :
    (S.invocation hh k).targetLabel =
      embeddedLabel (reindexedPrefix S.p0 S.a k) (S.a (k + 1)) := by
  rfl

/-- Additive centre/side directional counts over any finite prefix of the
    recursive schedule. -/
noncomputable def FrameTowerSchedule.totalCentreSteps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (S.invocation hh k).centreSteps

noncomputable def FrameTowerSchedule.totalSideSteps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (S.invocation hh k).sideSteps

noncomputable def FrameTowerSchedule.totalDirectionSteps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (S.invocation hh k).directionSteps

theorem FrameTowerSchedule.total_centre_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    S.totalCentreSteps hh n = n * h := by
  have hcount := reindexedStage_counts hh S.p0 S.a S.prefix_unit
    S.active_unit S.active_step_orthogonal
  simp only [FrameTowerSchedule.totalCentreSteps]
  simp [FrameLabelledInvocation, hcount]

theorem FrameTowerSchedule.total_side_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    S.totalSideSteps hh n = n * (h - 2) := by
  have hcount := reindexedStage_counts hh S.p0 S.a S.prefix_unit
    S.active_unit S.active_step_orthogonal
  simp only [FrameTowerSchedule.totalSideSteps]
  simp [FrameLabelledInvocation, hcount]

theorem FrameTowerSchedule.total_direction_steps {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    S.totalDirectionSteps hh n = n * (2 * h - 2) := by
  calc
    S.totalDirectionSteps hh n =
        S.totalCentreSteps hh n + S.totalSideSteps hh n := by
      simp [FrameTowerSchedule.totalDirectionSteps,
        FrameTowerSchedule.totalCentreSteps,
        FrameTowerSchedule.totalSideSteps,
        FrameLabelledInvocation.directionSteps,
        Finset.sum_add_distrib, Nat.mul_add]
    _ = n * h + n * (h - 2) := by
      rw [S.total_centre_steps hh n, S.total_side_steps hh n]
    _ = n * (2 * h - 2) := by
      have hfactor : 2 * h - 2 = h + (h - 2) := by omega
      rw [hfactor]
      exact (Nat.mul_add n h (h - 2)).symm

/-- A finite schedule certificate: the local frame transition and all three
    additive direction ledgers are available simultaneously. -/
theorem FrameTowerSchedule.finite_certificate {h : ℕ}
    (S : FrameTowerSchedule h) (hh : 2 ≤ h) (n : ℕ) :
    (∀ k, finTowerLift (S.a (k + 1))
        (S.invocation hh k).sourceLabel =
      (S.invocation hh (k + 1)).sourceLabel) ∧
    S.totalCentreSteps hh n = n * h ∧
    S.totalSideSteps hh n = n * (h - 2) ∧
    S.totalDirectionSteps hh n = n * (2 * h - 2) := by
  exact ⟨fun k => S.invocation_boundary_transport hh k,
    S.total_centre_steps hh n,
    S.total_side_steps hh n,
    S.total_direction_steps hh n⟩

end CenterAllLengthBridge
end ExactFourier
end OAI
