import OAI.Computability.FourierCircuit.CenterBoundaryTensorLift
import OAI.Computability.FourierCircuit.StagePrefixLabelAudit
import Mathlib.Tactic

/-!
# Cross-prefix transport for the finite address tower

`CenterBoundaryTensorLift` transports an active-factor shear while the
prefix type is fixed.  The physical three-stage construction also changes
the prefix type: an old address `ι × Fin h` becomes the next prefix
`(ι × Fin h)`.  This file isolates that missing linear-algebra interface.

The map `tensorLift q` appends a unit active label `q` to an old address
vector.  It preserves the binary dot product, and sends an inserted old
label `p ⊗ a` to the next-stage inserted label `(p ⊗ a) ⊗ q`.  Iterating it
gives a finite tower of frame labels with adjacent stages sharing the full
label from the preceding stage.  No gate semantics or cost claim is made.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterStageTowerTransport

abbrev F := ZMod 2
abbrev Active (h : ℕ) := Fin h → F

/-! A prefix is an iterated product of active coordinates. -/

def TowerPrefix (h : ℕ) : ℕ → Type
  | 0 => PUnit
  | k + 1 => TowerPrefix h k × Fin h

instance towerPrefixFintype (h k : ℕ) : Fintype (TowerPrefix h k) := by
  induction k with
  | zero => change Fintype PUnit; exact inferInstance
  | succ k ih =>
      change Fintype (TowerPrefix h k × Fin h)
      exact inferInstance

instance towerPrefixDecidableEq (h k : ℕ) : DecidableEq (TowerPrefix h k) := by
  induction k with
  | zero => change DecidableEq PUnit; exact inferInstance
  | succ k ih =>
      change DecidableEq (TowerPrefix h k × Fin h)
      exact inferInstance

theorem towerPrefix_card (h k : ℕ) :
    Fintype.card (TowerPrefix h k) = h ^ k := by
  induction k with
  | zero => simp [TowerPrefix]
  | succ k ih =>
      change Fintype.card (TowerPrefix h k × Fin h) = h ^ (k + 1)
      simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

noncomputable def towerPrefixFinEquiv (h k : ℕ) :
    TowerPrefix h k ≃ Fin (h ^ k) :=
  (Fintype.equivFin (TowerPrefix h k)).trans
    (finCongr (towerPrefix_card h k))

/-! A product-order equivalence, useful when comparing the abstract tower
with the concrete `Fin (h ^ k)` address convention.  Unlike
`Fintype.equivFin`, this recursively uses `finProdFinEquiv`; it therefore
keeps the old prefix coordinates as the first factor at every extension. -/

noncomputable def towerPrefixProductFinEquiv (h : ℕ) : (k : ℕ) →
    TowerPrefix h k ≃ Fin (h ^ k)
  | 0 =>
      (Fintype.equivFin (TowerPrefix h 0)).trans
        (finCongr (by simp [TowerPrefix]))
  | k + 1 =>
      ((towerPrefixProductFinEquiv h k).prodCongr (Equiv.refl (Fin h))).trans
        finProdFinEquiv

/-! Reindexing along a prefix equivalence is an isometry for the binary dot
product and commutes with tensor insertion.  This is the exact coordinate
bridge one may use with `towerPrefixProductFinEquiv`; it still says nothing
about whether the induced permutation is available in the gate model. -/

def prefixReindex {α β : Type*} (e : α ≃ β)
    (p : α → F) : β → F := p ∘ e.symm

def addressReindex {α β : Type*} {h : ℕ} (e : α ≃ β)
    (v : α × Fin h → F) : β × Fin h → F :=
  v ∘ (e.prodCongr (Equiv.refl (Fin h))).symm

theorem prefixReindex_dot {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p q : α → F) :
    dotProduct (prefixReindex e p) (prefixReindex e q) =
      dotProduct p q := by
  change (∑ y : β, p (e.symm y) * q (e.symm y)) = _
  exact Fintype.sum_equiv e.symm
    (fun y => p (e.symm y) * q (e.symm y))
    (fun x => p x * q x) (fun _ => rfl)

theorem addressReindex_insert {α β : Type*} {h : ℕ}
    (e : α ≃ β) (p : α → F) (a : Active h) :
    addressReindex e (CenterRowGeneral.insert p a) =
      CenterRowGeneral.insert (prefixReindex e p) a := by
  funext z
  rfl

abbrev PrefixLabel (h k : ℕ) := TowerPrefix h k → F
abbrev Address (h k : ℕ) := TowerPrefix h k × Fin h → F

/-! Appending one active factor to an address vector. -/

def tensorLift {h k : ℕ} (q : Active h)
    (v : Address h k) : Address h (k + 1) :=
  fun r => v r.1 * q r.2

@[simp] theorem tensorLift_apply {h k : ℕ} (q : Active h)
    (v : Address h k) (r : TowerPrefix h (k + 1) × Fin h) :
    tensorLift q v r = v r.1 * q r.2 := rfl

theorem tensorLift_dot_general {h k : ℕ} (q q' : Active h)
    (v v' : Address h k) :
    dotProduct (tensorLift q v) (tensorLift q' v') =
      dotProduct v v' * dotProduct q q' := by
  change (∑ r : TowerPrefix h (k + 1) × Fin h,
      (v r.1 * q r.2) * (v' r.1 * q' r.2)) = _
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : TowerPrefix h (k + 1), ∑ j : Fin h,
        (v i * q j) * (v' i * q' j)) =
      ∑ i : TowerPrefix h (k + 1),
        (v i * v' i) * (∑ j : Fin h, q j * q' j) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j : Fin h, (v i * q j) * (v' i * q' j)) =
            ∑ j : Fin h, (v i * v' i) * (q j * q' j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (v i * v' i) * (∑ j : Fin h, q j * q' j) := by
          rw [Finset.mul_sum]
    _ = (∑ i : TowerPrefix h (k + 1), v i * v' i) *
        (∑ j : Fin h, q j * q' j) := by
      rw [Finset.sum_mul]

theorem tensorLift_dot_of_unit {h k : ℕ} (q : Active h)
    (hq : dotProduct q q = (1 : F)) (v v' : Address h k) :
    dotProduct (tensorLift q v) (tensorLift q v') =
      dotProduct v v' := by
  rw [tensorLift_dot_general, hq, mul_one]

/-! Compatibility with the centre-row insertion map. -/

theorem tensorLift_insert {h k : ℕ} (p : PrefixLabel h k)
    (a q : Active h) :
    tensorLift q (CenterRowGeneral.insert p a) =
      CenterRowGeneral.insert (CenterRowGeneral.insert p a) q := by
  funext r
  rfl

theorem tensorLift_insert_dot_of_unit {h k : ℕ} (p : PrefixLabel h k)
    (hp : dotProduct p p = (1 : F))
    (a q : Active h)
    (ha : dotProduct a a = (1 : F))
    (hq : dotProduct q q = (1 : F)) :
    dotProduct
        (CenterRowGeneral.insert (CenterRowGeneral.insert p a) q)
        (CenterRowGeneral.insert (CenterRowGeneral.insert p a) q) =
      (1 : F) := by
  rw [← tensorLift_insert]
  exact (tensorLift_dot_of_unit q hq
    (CenterRowGeneral.insert p a) (CenterRowGeneral.insert p a)).trans (by
      rw [CenterRowGeneral.insert_dot_insert p hp, ha]
      )

/-! The finite tower of prefixes generated by an active-label sequence. -/

noncomputable def towerPrefix (h : ℕ) (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) : (k : ℕ) → PrefixLabel h k
  | 0 => p0
  | k + 1 => CenterRowGeneral.insert (towerPrefix h p0 a k) (a k)

noncomputable def towerLabel (h : ℕ) (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) : Address h k :=
  CenterRowGeneral.insert (towerPrefix h p0 a k) (a k)

theorem towerLabel_eq_next_prefix (h : ℕ) (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) :
    towerLabel h p0 a k = towerPrefix h p0 a (k + 1) := by
  rfl

theorem towerPrefix_unit (h : ℕ) (p0 : PrefixLabel h 0)
    (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F)) :
    ∀ k, dotProduct (towerPrefix h p0 a k)
      (towerPrefix h p0 a k) = (1 : F) := by
  intro k
  induction k with
  | zero => exact hp0
  | succ k ih =>
      change dotProduct
          (CenterRowGeneral.insert (towerPrefix h p0 a k) (a k))
          (CenterRowGeneral.insert (towerPrefix h p0 a k) (a k)) = 1
      rw [CenterRowGeneral.insert_dot_insert _ ih, ha]

theorem towerLabel_unit (h : ℕ) (p0 : PrefixLabel h 0)
    (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F)) (k : ℕ) :
    dotProduct (towerLabel h p0 a k) (towerLabel h p0 a k) = (1 : F) := by
  rw [towerLabel]
  rw [CenterRowGeneral.insert_dot_insert _ (towerPrefix_unit h p0 a hp0 ha k)]
  exact ha k

theorem towerTransition {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h) (k : ℕ) :
    tensorLift (a (k + 1)) (towerLabel h p0 a k) =
      towerLabel h p0 a (k + 1) := by
  rw [towerLabel, towerLabel]
  rfl

theorem towerTransition_norm {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F)) (k : ℕ) :
    dotProduct
        (tensorLift (a (k + 1)) (towerLabel h p0 a k))
        (tensorLift (a (k + 1)) (towerLabel h p0 a k)) = (1 : F) := by
  rw [tensorLift_dot_of_unit (a (k + 1)) (ha (k + 1))]
  exact towerLabel_unit h p0 a hp0 ha k

/-! The precise cross-prefix interface available to the schedule layer. -/

theorem tower_stage_interface {h : ℕ} (p0 : PrefixLabel h 0)
    (a : ℕ → Active h)
    (hp0 : dotProduct p0 p0 = (1 : F))
    (ha : ∀ k, dotProduct (a k) (a k) = (1 : F))
    (haa : ∀ k, dotProduct (a k) (a (k + 1)) = (0 : F)) (k : ℕ) :
    dotProduct (towerLabel h p0 a k) (towerLabel h p0 a k) = (1 : F) ∧
      dotProduct (a k) (a (k + 1)) = (0 : F) ∧
      tensorLift (a (k + 1)) (towerLabel h p0 a k) =
        towerLabel h p0 a (k + 1) ∧
      towerLabel h p0 a k = towerPrefix h p0 a (k + 1) := by
  exact ⟨towerLabel_unit h p0 a hp0 ha k, haa k,
    towerTransition p0 a k,
    towerLabel_eq_next_prefix h p0 a k⟩

end CenterStageTowerTransport
end ExactFourier
end OAI
