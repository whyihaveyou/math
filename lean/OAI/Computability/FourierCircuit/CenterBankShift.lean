import OAI.Computability.FourierCircuit.CenterMap
import Mathlib.Tactic

/-!
# The commuting square behind centre-line compression

The original centre bank has `h + 1` coordinates: `h` incidence sums and one
global sum.  The compressed bank stores

`c'_j = c_j - q/3`.

This file proves the exact three identities needed to replace the old bank in
the scalar eight-row invocation: the shifted old source map is the new source
map, old readout equals compressed readout after shifting, and shifting
commutes with an old-bank update.  The shift is deliberately not called an
invertible change of frame: it is a surjective map from an `(h+1)`-wire bank
to an `h`-wire bank.
-/

namespace OAI
namespace ExactFourier
namespace CenterBankShift

open CenterCompression

abbrev CenterBank (h : ℕ) (K : Type*) := (Fin h → K) × K

variable {h : ℕ} {K : Type*} [Field K] [CharZero K]

/-- The centre source map before eliminating the global coordinate. -/
def oldG (x : Triple h → K) : CenterBank h K :=
  (fun j => ∑ T ∈ (tripleSet h).attach,
      if j ∈ T.1 then x T else 0,
    ∑ T ∈ (tripleSet h).attach, x T)

/-- The linear-looking shift used by the compressed bank. -/
def shift (c : CenterBank h K) : Fin h → K :=
  fun j => c.1 j - c.2 / (3 : K)

/-- The old readout, retaining its global centre coordinate. -/
def oldR (S : Triple h) (c : CenterBank h K) : K :=
  (∑ j ∈ S.1, c.1 j - c.2) / (2 : K)

theorem shift_oldG (x : Triple h → K) :
    shift (oldG x) = compressedG x := by
  funext j
  rfl

theorem oldR_shift (S : Triple h) (c : CenterBank h K) :
    oldR S c = compressedR S (shift c) := by
  unfold oldR compressedR shift
  symm
  exact three_point_shift S.1 (triple_card S) c.1 c.2

theorem shift_add (u v : CenterBank h K) :
    shift (u.1 + v.1, u.2 + v.2) = shift u + shift v := by
  funext j
  dsimp [shift]
  ring

theorem shift_old_update (c : CenterBank h K) (x : Triple h → K) :
    shift (c.1 + (oldG x).1, c.2 + (oldG x).2) =
      shift c + compressedG x := by
  rw [shift_add, shift_oldG]

theorem shift_surjective : Function.Surjective (shift (h := h) (K := K)) := by
  intro d
  refine ⟨(d, 0), ?_⟩
  funext j
  simp [shift]

theorem oldR_shift_oldG (S : Triple h) (x : Triple h → K) :
    oldR S (oldG x) = compressedR S (compressedG x) := by
  rw [oldR_shift, shift_oldG]

end CenterBankShift
end ExactFourier
end OAI
