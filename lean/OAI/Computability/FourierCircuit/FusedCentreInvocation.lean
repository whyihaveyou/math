import OAI.Computability.FourierCircuit.CompressedInvocation

/-!
# Scalar fused-centre invocation

This file isolates the algebraic interface suggested by the reversible
centre-boundary shear candidate.  The centre update `c ↦ c + G x` and its
immediate readout are fused into the single update
`y ↦ y + R (c + G x)`.  The centre bank is therefore left unchanged, while
an arbitrary side bank is still restored.  This is a scalar interface only:
it does not assert that the fused map is an admissible tensor gate or that its
six rows have a global frame-labelled schedule.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreInvocation

open CompressedInvocation

section Generic

variable {X A C : Type*} [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

/-- The six scalar rows after fusing the centre update with its readout. -/
def fusedRows (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : State X A C) : State X A C :=
  let s0 := {s with y := s.y - J s.side}
  let s1 := {s0 with y := s0.y - R s0.center}
  let s2 := {s1 with side := s1.side + V s1.x}
  let s3 := {s2 with y := s2.y + R (s2.center + G s2.x)}
  let s4 := {s3 with y := s3.y + J s3.side}
  {s4 with side := s4.side - V s4.x}

/-- Reverse six rows for the fused invocation. -/
def inverseFusedRows (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : State X A C) : State X A C :=
  let s0 := {s with side := s.side + V s.x}
  let s1 := {s0 with y := s0.y - J s0.side}
  let s2 := {s1 with y := s1.y - R (s1.center + G s1.x)}
  let s3 := {s2 with side := s2.side - V s2.x}
  let s4 := {s3 with y := s3.y + R s3.center}
  {s4 with y := s4.y + J s4.side}

/-- The fused rows implement the same shear as the original eight rows. -/
theorem fusedRows_restore (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    fusedRows R G J V s = {s with y := s.y + s.x} := by
  cases s with
  | mk x y a c =>
    simp only [fusedRows, map_add]
    have hy : y - J a - R c + (R c + R (G x)) + (J a + J (V x)) = y + x := by
      calc
        _ = y + (R (G x) + J (V x)) := by abel
        _ = y + x := by rw [hidentity]
    rw [hy]
    simp

/-- The reversed fused rows subtract the source shear and restore both banks. -/
theorem inverseFusedRows_restore
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    inverseFusedRows R G J V s = {s with y := s.y - s.x} := by
  cases s with
  | mk x y a c =>
    simp only [inverseFusedRows, map_add, add_sub_cancel_right]
    have hy : y - (J a + J (V x)) - (R c + R (G x)) + R c + J a = y - x := by
      calc
        _ = y - (R (G x) + J (V x)) := by abel
        _ = y - x := by rw [hidentity]
    rw [hy]

/-- The reversed fused schedule is a two-sided inverse. -/
theorem inverseFusedRows_fusedRows
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    inverseFusedRows R G J V (fusedRows R G J V s) = s := by
  rw [fusedRows_restore R G J V hidentity,
    inverseFusedRows_restore R G J V hidentity]
  cases s
  simp

/-- The forward fused schedule is also a two-sided inverse. -/
theorem fusedRows_inverseFusedRows
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    fusedRows R G J V (inverseFusedRows R G J V s) = s := by
  rw [inverseFusedRows_restore R G J V hidentity,
    fusedRows_restore R G J V hidentity]
  cases s
  simp

/-- Three fused invocations exchange the two logical source registers. -/
def fusedThreeInvocations (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : State X A C) : State X A C :=
  let s1 := fusedRows R G J V s
  let s2 := {s1 with x := s1.y, y := s1.x}
  let s3 := inverseFusedRows R G J V s2
  let s4 := {s3 with x := s3.y, y := s3.x}
  fusedRows R G J V s4

theorem fusedThreeInvocations_exchange
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x) (s : State X A C) :
    fusedThreeInvocations R G J V s = {s with x := -s.y, y := s.x} := by
  cases s with
  | mk x y a c =>
    simp only [fusedThreeInvocations, fusedRows_restore R G J V hidentity,
      inverseFusedRows_restore R G J V hidentity]
    abel

end Generic

namespace OrderedPairs

open CenterCompression
open CompressedInvocation.OrderedPairs

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

/-- The centre-compressed h=24 scalar instance of the fused schedule. -/
theorem compressed_fused_restore
    (s : State (Triple h → K) (SideBank h K) (Fin h → K)) :
    fusedRows RHom compressedG JHom V s = {s with y := s.y + s.x} := by
  exact @fusedRows_restore (Triple h → K) (SideBank h K) (Fin h → K)
    _ _ _ RHom compressedG JHom V identity s

/-- Its reverse restores an arbitrary compressed centre/side bank. -/
theorem compressed_inverse_fused_restore
    (s : State (Triple h → K) (SideBank h K) (Fin h → K)) :
    inverseFusedRows RHom compressedG JHom V s = {s with y := s.y - s.x} := by
  exact @inverseFusedRows_restore (Triple h → K) (SideBank h K) (Fin h → K)
    _ _ _ RHom compressedG JHom V identity s

theorem compressed_fused_exchange
    (s : State (Triple h → K) (SideBank h K) (Fin h → K)) :
    fusedThreeInvocations RHom compressedG JHom V s = {s with x := -s.y, y := s.x} := by
  exact @fusedThreeInvocations_exchange (Triple h → K) (SideBank h K) (Fin h → K)
    _ _ _ RHom compressedG JHom V identity s

end OrderedPairs
end FusedCentreInvocation
end ExactFourier
end OAI
