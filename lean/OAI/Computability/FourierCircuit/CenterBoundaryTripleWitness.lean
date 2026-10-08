import OAI.Computability.FourierCircuit.CenterBoundarySelectiveTransvection
import OAI.Computability.FourierCircuit.CenterBoundaryShearCandidate
import OAI.Computability.FourierCircuit.FrameLabels
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# A uniform h = 24 witness for centre-boundary shears

For every three-element active label `T ⊂ Fin 24`, there is an unused
coordinate.  The complement therefore has cardinality 21, and the indicator
of `T` vanishes at that coordinate.  This file packages that finite witness
with the existing local centre-boundary transport certificates, for an
arbitrary finite prefix unit `p`.

The resulting statements are local label certificates.  They do not assert
that the binary transvection is one legal complex gate, nor do they provide a
global fixed-width schedule or an all-length Fourier recursion.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace CenterBoundaryTripleWitness

open FrameLabels
open BinaryTransvection
open CenterBoundaryShearCandidate
open CenterBoundarySelectiveTransvection
open SideRowGeneralArbitrary

abbrev F := ZMod 2
abbrev H := 24
abbrev Active := Fin H → F

/-! ## The finite witness and its exact complement count -/

theorem complement_card (T : Finset (Fin H)) (hT : T.card = 3) :
    (Finset.univ \ T).card = 21 := by
  simp [Finset.card_sdiff, hT, H]

theorem exists_unused_coordinate (T : Finset (Fin H)) (hT : T.card = 3) :
    ∃ w : Fin H, w ∉ T := by
  have hlt : T.card < (Finset.univ : Finset (Fin H)).card := by
    rw [hT, Finset.card_univ]
    decide
  obtain ⟨w, _hwuniv, hwT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨w, hwT⟩

theorem indicator_zero_at_unused (T : Finset (Fin H))
    (w : Fin H) (hwT : w ∉ T) :
    indicator T w = 0 := by
  simp [indicator, hwT]

/-- The complete finite witness package used by the local transport. -/
theorem exists_witness (T : Finset (Fin H)) (hT : T.card = 3) :
    ∃ w : Fin H,
      w ∉ T ∧
      (Finset.univ \ T).card = 21 ∧
      indicator T w = 0 := by
  obtain ⟨w, hwT⟩ := exists_unused_coordinate T hT
  refine ⟨w, hwT, complement_card T hT, ?_⟩
  exact indicator_zero_at_unused T w hwT

/-! ## Unit target labels and local shear transport -/

theorem indicator_unit (T : Finset (Fin H)) (hT : T.card = 3) :
    dotProduct (indicator T) (indicator T) = (1 : F) := by
  change FrameLabels.dotForm (indicator T) (indicator T) = (1 : F)
  simpa [FrameLabels.dotForm, BinaryTransvection.bilinearDot] using
    (FrameLabels.indicator_triple_norm T hT)

theorem sheared_target_legal
    {ι : Type*} [Fintype ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (T : Finset (Fin H)) (hT : T.card = 3)
    (w : Fin H) (hwT : w ∉ T) :
    insertP p
        (unitCoordinateEquiv (indicator T) w (indicator_unit T hT)
          (indicator_zero_at_unused T w hwT) (indicator T)) ∈
      L5 p (indicator T) := by
  exact CenterBoundaryShearCandidate.sheared_insert_mem_L5
    p (indicator T) hp (indicator_unit T hT) w
      (indicator_zero_at_unused T w hwT)

/-! ## Selective full-address transport at an arbitrary prefix -/

theorem selective_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → F) (x : Active) (hp : dotProduct p p = (1 : F))
    (T : Finset (Fin H)) (hT : T.card = 3)
    (w : Fin H) (hwT : w ∉ T)
    (hxt : dotProduct x (indicator T) = 0)
    (hxw : x w = 0)
    (z : CenterBoundarySelectiveTransvection.Address ι H)
    (hz : z ∈ L2 p x) :
    W p (indicator T) w
        (z + d p (indicator T)) = z + e p w := by
  exact CenterBoundarySelectiveTransvection.W_map_source_plus_d
    p x (indicator T) w hp (indicator_unit T hT) hxt
      (indicator_zero_at_unused T w hwT) hxw z hz

theorem selective_transport_legal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → F) (x : Active) (hp : dotProduct p p = (1 : F))
    (T : Finset (Fin H)) (hT : T.card = 3)
    (w : Fin H) (hwT : w ∉ T)
    (hxt : dotProduct x (indicator T) = 0)
    (hxw : x w = 0)
    (z : CenterBoundarySelectiveTransvection.Address ι H)
    (hz : z ∈ L2 p x) :
    W p (indicator T) w
        (z + d p (indicator T)) ∈ L5 p (indicator T) := by
  exact CenterBoundarySelectiveTransvection.W_map_source_plus_d_mem_L5
    p x (indicator T) w hp (indicator_unit T hT) hxt
      (indicator_zero_at_unused T w hwT) hxw z hz

/-- Every target triple has a local reversible repair at every unit prefix.
The source-fixing clause retains its necessary zero-coordinate premise. -/
theorem exists_local_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (T : Finset (Fin H)) (hT : T.card = 3) :
    ∃ w : Fin H,
      w ∉ T ∧
      (Finset.univ \ T).card = 21 ∧
      indicator T w = 0 ∧
      W p (indicator T) w (d p (indicator T)) = e p w ∧
      e p w ∈ L5 p (indicator T) ∧
      Function.Involutive (W p (indicator T) w) ∧
      (∀ x : Active, dotProduct x (indicator T) = 0 → x w = 0 →
        ∀ z ∈ L2 p x,
          W p (indicator T) w (z + d p (indicator T)) ∈ L5 p (indicator T)) := by
  obtain ⟨w, hwT, hcard, hw⟩ := exists_witness T hT
  refine ⟨w, hwT, hcard, hw, ?_, ?_, ?_, ?_⟩
  · exact CenterBoundarySelectiveTransvection.W_map_d_to_e
      p (indicator T) w hp (indicator_unit T hT) hw
  · exact CenterBoundarySelectiveTransvection.e_mem_L5
      p (indicator T) w hp hw
  · exact CenterBoundarySelectiveTransvection.W_involutive
      p (indicator T) w hp (indicator_unit T hT) hw
  · intro x hxt hxw z hz
    exact selective_transport_legal p x hp T hT w hwT hxt hxw z hz

/-- The active-factor shear certificate is also available uniformly in the
target triple and the prefix, using the same finite witness. -/
theorem exists_sheared_target_legal
    {ι : Type*} [Fintype ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (T : Finset (Fin H)) (hT : T.card = 3) :
    ∃ (w : Fin H) (hwT : w ∉ T),
      insertP p
          (unitCoordinateEquiv (indicator T) w (indicator_unit T hT)
            (indicator_zero_at_unused T w hwT) (indicator T)) ∈
        L5 p (indicator T) := by
  obtain ⟨w, hwT⟩ := exists_unused_coordinate T hT
  exact ⟨w, hwT, sheared_target_legal p hp T hT w hwT⟩

/-! ## A simultaneous witness for an orthogonal source/target pair -/

/-- The number of coordinates unused by two triples is exact, including
overlap.  In particular it is always at least 18. -/
theorem pair_complement_card
    (S T : Finset (Fin H)) (hS : S.card = 3) (hT : T.card = 3) :
    (Finset.univ \ (S ∪ T)).card = 18 + (S ∩ T).card := by
  have hunion := Finset.card_union_add_card_inter S T
  have hcard : (Finset.univ \ (S ∪ T)).card = 24 - (S ∪ T).card := by
    simp [Finset.card_sdiff, H]
  rw [hcard]
  omega

theorem exists_simultaneous_unused_coordinate
    (S T : Finset (Fin H)) (hS : S.card = 3) (hT : T.card = 3) :
    ∃ w : Fin H, w ∉ S ∧ w ∉ T := by
  have hlt : (S ∪ T).card < (Finset.univ : Finset (Fin H)).card := by
    have hunion := Finset.card_union_le S T
    rw [Finset.card_univ, Fintype.card_fin]
    change (S ∪ T).card < 24
    omega
  obtain ⟨w, _hwuniv, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, ?_, ?_⟩
  · exact fun hwS => hw (Finset.mem_union_left T hwS)
  · exact fun hwT => hw (Finset.mem_union_right S hwT)

theorem indicators_orthogonal
    (S T : Finset (Fin H)) (heven : Even (S ∩ T).card) :
    dotProduct (indicator S) (indicator T) = (0 : F) := by
  change FrameLabels.dotForm (indicator S) (indicator T) = (0 : F)
  exact FrameLabels.indicator_orthogonal_of_even T S
    (by simpa [Finset.inter_comm] using heven)

/-- For each even-intersection pair of source and target triples, there is
one reversible selective transport which fixes the old source row and makes
the fused readout legal.  Its existence is local to this pair. -/
theorem exists_pair_local_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → F) (hp : dotProduct p p = (1 : F))
    (S T : Finset (Fin H)) (hS : S.card = 3) (hT : T.card = 3)
    (heven : Even (S ∩ T).card) :
    ∃ w : Fin H,
      w ∉ S ∧ w ∉ T ∧
      (Finset.univ \ (S ∪ T)).card = 18 + (S ∩ T).card ∧
      Function.Involutive (W p (indicator T) w) ∧
      (∀ z ∈ L2 p (indicator S), W p (indicator T) w z = z) ∧
      (∀ z ∈ L2 p (indicator S),
        W p (indicator T) w (z + d p (indicator T)) = z + e p w) ∧
      (∀ z ∈ L2 p (indicator S),
        W p (indicator T) w (z + d p (indicator T)) ∈ L5 p (indicator T)) := by
  obtain ⟨w, hwS, hwT⟩ := exists_simultaneous_unused_coordinate S T hS hT
  have hxt := indicators_orthogonal S T heven
  have hxw := indicator_zero_at_unused S w hwS
  have htw := indicator_zero_at_unused T w hwT
  refine ⟨w, hwS, hwT, pair_complement_card S T hS hT, ?_, ?_, ?_, ?_⟩
  · exact CenterBoundarySelectiveTransvection.W_involutive
      p (indicator T) w hp (indicator_unit T hT) htw
  · intro z hz
    exact CenterBoundarySelectiveTransvection.W_fix_L2
      p (indicator S) (indicator T) w hp hxt hxw z hz
  · intro z hz
    exact selective_transport p (indicator S) hp T hT w hwT hxt hxw z hz
  · intro z hz
    exact selective_transport_legal p (indicator S) hp T hT w hwT hxt hxw z hz

end CenterBoundaryTripleWitness
end ExactFourier
end OAI
