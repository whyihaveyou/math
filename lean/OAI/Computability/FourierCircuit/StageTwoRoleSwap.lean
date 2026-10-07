import OAI.Computability.FourierCircuit.CompressedInvocation
import Mathlib.Tactic

/-!
# Stage-2 side-role reindexing

The middle Fourier stage runs the same scalar eight-row invocation with
logical source `Y` and target `X`.  Its side roles therefore have their two
triple endpoints exchanged.  This file isolates the finite reindexing facts:
legality is symmetric, the exchange is an involutive equivalence, and the
side coefficient is unchanged by the exchange.  It is a role-index audit, not
the missing global frame-labelled stage proof.
-/

namespace OAI
namespace ExactFourier
namespace StageTwoRoleSwap

open CenterCompression
open CompressedInvocation.OrderedPairs

theorem allowed_comm {h : ℕ} (S T : Triple h) :
    Allowed S T ↔ Allowed T S := by
  constructor
  · rintro ⟨hne, heven⟩
    exact ⟨Ne.symm hne, by simpa [Finset.inter_comm] using heven⟩
  · rintro ⟨hne, heven⟩
    exact ⟨Ne.symm hne, by simpa [Finset.inter_comm] using heven⟩

def swapRole {h : ℕ} (r : Role h) : Role h :=
  ⟨r.source, r.target, (allowed_comm r.target r.source).mp r.admissible⟩

theorem swapRole_target {h : ℕ} (r : Role h) :
    (swapRole r).target = r.source := rfl

theorem swapRole_source {h : ℕ} (r : Role h) :
    (swapRole r).source = r.target := rfl

theorem swapRole_admissible {h : ℕ} (r : Role h) :
    Allowed (swapRole r).target (swapRole r).source :=
  (swapRole r).admissible

def swapEquiv (h : ℕ) : Role h ≃ Role h where
  toFun := swapRole
  invFun := swapRole
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro r
    cases r
    rfl

theorem sideCoeff_swap {h : ℕ} {K : Type*} [Field K]
    (S T : Triple h) :
    sideCoeff (K := K) S T = sideCoeff (K := K) T S := by
  by_cases hST : S = T
  · subst T
    rfl
  · simp only [sideCoeff, hST, Ne.symm hST, Finset.inter_comm]

def swapBank {h : ℕ} {K : Type*} (a : SideBank h K) : SideBank h K :=
  fun r => a (swapRole r)

theorem swapBank_involutive {h : ℕ} {K : Type*} (a : SideBank h K) :
    swapBank (swapBank a) = a := by
  funext r
  cases r
  rfl

end StageTwoRoleSwap
end ExactFourier
end OAI
