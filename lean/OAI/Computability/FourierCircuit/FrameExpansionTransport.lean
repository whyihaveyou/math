import OAI.Computability.FourierCircuit.SlotAssembly

/-!
# Frame embedding preserves the charged call list

The packing semantics treats monomial changes of coordinates as free steps and
charges only calls to a non-monomial matrix.  A framed gate can therefore be
expanded from an address type `α` to a larger address type `β` by an embedding:
the old monomial prefix and the active tuple are both embedded.  This file
proves that the resulting frame has the expected embedded matrix and that its
word has exactly the same call list.

This embeds a matrix on scalar wires and leaves spectator wires unchanged.
It does not identify scalar wires with binary label coordinates, implement a
dimension-increasing tensor lift, or establish a directional saving.
-/

namespace OAI
namespace ExactFourier
namespace Packing

noncomputable section

variable {τ : Type} {D : τ → Type}
  [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
  {A : ∀ t, Matrix (D t) (D t) ℂ}
  {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-! ## Expanding one frame -/

def Frame.embed (e : α ↪ β) (f : Frame D α) : Frame D β where
  mono := Embedded.matrix e f.mono
  monomial := f.monomial.embed e
  type := f.type
  tuple := f.tuple.trans e

@[simp] theorem Frame.embed_matrix (e : α ↪ β) (f : Frame D α) :
    (f.embed e).matrix (A := A) = Embedded.matrix e (f.matrix (A := A)) := by
  change Embedded.matrix e f.mono *
      Embedded.matrix (f.tuple.trans e) (A f.type) =
      Embedded.matrix e (f.mono * Embedded.matrix f.tuple (A f.type))
  rw [← Embedded.matrix_comp, ← Embedded.matrix_mul]

@[simp] theorem Frame.embed_word (e : α ↪ β) (f : Frame D α) :
    (f.word (A := A)).embed e = (f.embed e).word (A := A) := by
  rfl

theorem Frame.embed_calls (e : α ↪ β) (f : Frame D α) :
    (f.embed e).word (A := A).calls = [f.type] := by
  rfl

theorem Frame.embed_count [DecidableEq τ] (e : α ↪ β) (f : Frame D α) (t : τ) :
    (f.embed e).word (A := A).count t = if t = f.type then 1 else 0 := by
  rw [Word.count, Frame.embed_calls]
  by_cases h : t = f.type
  · simp [h]
  · have h' : f.type ≠ t := Ne.symm h
    rw [List.count_cons_of_ne h', List.count_nil]
    simp [h]

theorem Frame.embed_matrix_word (e : α ↪ β) (f : Frame D α) :
    (f.embed e).word (A := A).matrix =
      Embedded.matrix e (f.matrix (A := A)) := by
  rw [← Frame.embed_word, Word.matrix_embed, Frame.matrix_word]

end

end Packing
end ExactFourier
end OAI
