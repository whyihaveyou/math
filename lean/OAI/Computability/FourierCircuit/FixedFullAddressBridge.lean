import OAI.Computability.FourierCircuit.TensorFrameLabels
import Mathlib.Tactic

/-!
# Fixed-width full-address labels with spectators

The explicit construction uses one fixed binary address space for every
physical role.  A stage label has an active triple factor and may be tensored
with an arbitrary future (spectator) factor `Q`; the latter is retained while
the active stage is changed.  This file records that interface without
changing the address width.

`finTowerLift` is intentionally not used here: it changes `Fin (h ^ k)` to
`Fin (h ^ (k + 1))`, so it cannot be a same-width wire permutation.  The
definitions below keep the triple address and spectator type fixed and prove
the dot-product, unit, orthogonality, and reindexing facts needed before a
complex gate schedule is considered.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace FixedFullAddressBridge

open FrameLabels
open TensorFrameLabels

abbrev F := ZMod 2

/-! ## The fixed address type -/

abbrev TripleAddress (h : ℕ) := Fin h × (Fin h × Fin h)

abbrev FullAddress (h : ℕ) (Q : Type*) := TripleAddress h × Q

abbrev TripleLabel (h : ℕ) := TripleAddress h → F

abbrev FullLabel (h : ℕ) (Q : Type*) := FullAddress h Q → F

/-! A spectator tensor keeps the address width fixed. -/

def spectatorLift {h : ℕ} {Q : Type*}
    (q : Q → F) (v : TripleLabel h) : FullLabel h Q :=
  fun z => v z.1 * q z.2

@[simp] theorem spectatorLift_apply {h : ℕ} {Q : Type*}
    (q : Q → F) (v : TripleLabel h) (z : FullAddress h Q) :
    spectatorLift q v z = v z.1 * q z.2 := rfl

theorem spectatorLift_dot {h : ℕ} {Q : Type*} [Fintype Q]
    (q q' : Q → F) (v v' : TripleLabel h) :
    dotProduct (spectatorLift q v) (spectatorLift q' v') =
      dotProduct v v' * dotProduct q q' := by
  classical
  change (∑ z : TripleAddress h × Q,
      (v z.1 * q z.2) * (v' z.1 * q' z.2)) = _
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : TripleAddress h, ∑ y : Q,
        (v x * q y) * (v' x * q' y)) =
        ∑ x : TripleAddress h, (v x * v' x) *
          (∑ y : Q, q y * q' y) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ y : Q, (v x * q y) * (v' x * q' y)) =
            ∑ y : Q, (v x * v' x) * (q y * q' y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (v x * v' x) * (∑ y : Q, q y * q' y) := by
          rw [Finset.mul_sum]
    _ = (∑ x : TripleAddress h, v x * v' x) *
          (∑ y : Q, q y * q' y) := by
      rw [Finset.sum_mul]

theorem spectatorLift_unit {h : ℕ} {Q : Type*} [Fintype Q]
    (q : Q → F) (v : TripleLabel h)
    (hv : dotProduct v v = (1 : F))
    (hq : dotProduct q q = (1 : F)) :
    dotProduct (spectatorLift q v) (spectatorLift q v) = (1 : F) := by
  rw [spectatorLift_dot, hv, hq]
  simp

theorem spectatorLift_orthogonal {h : ℕ} {Q : Type*} [Fintype Q]
    (q q' : Q → F) (v v' : TripleLabel h)
    (hv : dotProduct v v' = (0 : F)) :
    dotProduct (spectatorLift q v) (spectatorLift q' v') = (0 : F) := by
  rw [spectatorLift_dot, hv, zero_mul]

/-! ## Concrete triple labels and fixed-width stage facts -/

def fullTripleLabel {h : ℕ} {Q : Type*}
    (A B C : Finset (Fin h)) (q : Q → F) : FullLabel h Q :=
  spectatorLift q (tensor3 A B C)

theorem fullTripleLabel_unit {h : ℕ} {Q : Type*} [Fintype Q]
    (A B C : Finset (Fin h)) (hA : A.card = 3)
    (hB : B.card = 3) (hC : C.card = 3)
    (q : Q → F) (hq : dotProduct q q = (1 : F)) :
    dotProduct (fullTripleLabel A B C q)
      (fullTripleLabel A B C q) = (1 : F) := by
  apply spectatorLift_unit q (tensor3 A B C)
  · exact tensor3_norm_of_triples A B C hA hB hC
  · exact hq

theorem fullTripleLabel_orthogonal_of_first {h : ℕ} {Q : Type*} [Fintype Q]
    (A B C A' B' C' : Finset (Fin h))
    (heven : Even (A ∩ A').card)
    (q q' : Q → F) :
    dotProduct (fullTripleLabel A B C q)
      (fullTripleLabel A' B' C' q') = (0 : F) := by
  apply spectatorLift_orthogonal q q' (tensor3 A B C) (tensor3 A' B' C')
  exact tensor3_orthogonal_of_even A B C A' B' C' heven

/-! ## Same-width frame reindexing -/

def fullReindex {h : ℕ} {Q R : Type*}
    (e : FullAddress h Q ≃ FullAddress h R)
    (v : FullLabel h Q) : FullLabel h R :=
  v ∘ e.symm

@[simp] theorem fullReindex_apply {h : ℕ} {Q R : Type*}
    (e : FullAddress h Q ≃ FullAddress h R)
    (v : FullLabel h Q) (z : FullAddress h R) :
    fullReindex e v z = v (e.symm z) := rfl

theorem fullReindex_left_inverse {h : ℕ} {Q R : Type*}
    (e : FullAddress h Q ≃ FullAddress h R) (v : FullLabel h Q) :
    fullReindex e.symm (fullReindex e v) = v := by
  funext z
  simp [fullReindex]

theorem fullReindex_right_inverse {h : ℕ} {Q R : Type*}
    (e : FullAddress h Q ≃ FullAddress h R) (v : FullLabel h R) :
    fullReindex e (fullReindex e.symm v) = v := by
  funext z
  simp [fullReindex]

theorem fullReindex_dot {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (v v' : FullLabel h Q) :
    dotProduct (fullReindex e v) (fullReindex e v') =
      dotProduct v v' := by
  change (∑ z : FullAddress h R,
      v (e.symm z) * v' (e.symm z)) = _
  exact Fintype.sum_equiv e.symm
    (fun z => v (e.symm z) * v' (e.symm z))
    (fun z => v z * v' z) (fun _ => rfl)

theorem fullReindex_unit {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (v : FullLabel h Q)
    (hv : dotProduct v v = (1 : F)) :
    dotProduct (fullReindex e v) (fullReindex e v) = (1 : F) := by
  rw [fullReindex_dot]
  exact hv

theorem fullReindex_orthogonal {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (v v' : FullLabel h Q)
    (hv : dotProduct v v' = (0 : F)) :
    dotProduct (fullReindex e v) (fullReindex e v') = (0 : F) := by
  rw [fullReindex_dot]
  exact hv

/-! Reindexing only the spectator factor is a useful special case. -/

def spectatorReindex {h : ℕ} {Q R : Type*}
    (e : Q ≃ R) (v : FullLabel h Q) : FullLabel h R :=
  fullReindex (Equiv.prodCongr (Equiv.refl (TripleAddress h)) e) v

theorem spectatorReindex_lift {h : ℕ} {Q R : Type*}
    (e : Q ≃ R) (q : Q → F) (v : TripleLabel h) :
    spectatorReindex e (spectatorLift q v) =
      spectatorLift (q ∘ e.symm) v := by
  funext z
  rfl

/-! A convenient fixed-width stage record for any spectator label. -/

structure FixedStage (h : ℕ) (Q : Type*) [Fintype Q] where
  source : FullLabel h Q
  target : FullLabel h Q
  source_unit : dotProduct (source : FullLabel h Q) source = (1 : F)
  target_unit : dotProduct (target : FullLabel h Q) target = (1 : F)
  source_target_orthogonal :
    dotProduct (source : FullLabel h Q) target = (0 : F)

def FixedStage.ofTriple {h : ℕ} {Q : Type*} [Fintype Q]
    (A B C A' B' C' : Finset (Fin h))
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hA' : A'.card = 3) (hB' : B'.card = 3) (hC' : C'.card = 3)
    (heven : Even (A ∩ A').card)
    (q q' : Q → F)
    (hq : dotProduct q q = (1 : F))
    (hq' : dotProduct q' q' = (1 : F)) :
    FixedStage h Q := by
  let source := fullTripleLabel A B C q
  let target := fullTripleLabel A' B' C' q'
  have hsource : dotProduct source source = (1 : F) := by
    dsimp [source]
    exact fullTripleLabel_unit A B C hA hB hC q hq
  have htarget : dotProduct target target = (1 : F) := by
    dsimp [target]
    exact fullTripleLabel_unit A' B' C' hA' hB' hC' q' hq'
  have horth : dotProduct source target = (0 : F) := by
    dsimp [source, target]
    exact fullTripleLabel_orthogonal_of_first A B C A' B' C' heven q q'
  exact ⟨source, target, hsource, htarget, horth⟩

def FixedStage.reindex {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (s : FixedStage h Q) : FixedStage h R :=
  { source := fullReindex e s.source
    target := fullReindex e s.target
    source_unit := fullReindex_unit e s.source s.source_unit
    target_unit := fullReindex_unit e s.target s.target_unit
    source_target_orthogonal := fullReindex_orthogonal e s.source s.target
      s.source_target_orthogonal }

theorem FixedStage.reindex_source {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (s : FixedStage h Q) :
    (s.reindex e).source = fullReindex e s.source := rfl

theorem FixedStage.reindex_target {h : ℕ} {Q R : Type*}
    [Fintype Q] [Fintype R]
    (e : FullAddress h Q ≃ FullAddress h R)
    (s : FixedStage h Q) :
    (s.reindex e).target = fullReindex e s.target := rfl

end FixedFullAddressBridge
end ExactFourier
end OAI
