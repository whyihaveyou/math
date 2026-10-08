import OAI.Computability.FourierCircuit.BinaryTransvection
import OAI.Computability.FourierCircuit.TensorFrameLabels

/-!
# A small interface for one residual stage

This file packages the local linear-algebra statement behind a residual
stage.  A certificate records a unit label `source` and a label `target`
orthogonal to it.  The main theorem is exactly the two-label decomposition
proved in `BinaryTransvection`.

The certificate deliberately contains no network, schedule, or operation
count.  Those data belong to a later layer of the all-length formalization.
The `pure3` constructor only connects this interface to the tensor-frame
lemmas; it does not assert that a complete Fourier stage has been built.
-/

open scoped BigOperators

namespace OAI
namespace ExactFourier
namespace StageResidual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Certificate (ι : Type*) [Fintype ι] [DecidableEq ι] where
  source : ι → ZMod 2
  target : ι → ZMod 2
  source_unit : dotProduct source source = (1 : ZMod 2)
  source_target_orthogonal : dotProduct source target = (0 : ZMod 2)

namespace Certificate

def parent (c : Certificate ι) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  ((ZMod 2) ∙ c.target).orthogonalBilin
    (BinaryTransvection.bilinearDot : _)

def removed (c : Certificate ι) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  (ZMod 2) ∙ c.source

def residual (c : Certificate ι) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  (Submodule.span (ZMod 2) ({c.source, c.target} : Set (ι → ZMod 2))).orthogonalBilin
    (BinaryTransvection.bilinearDot : _)

theorem decomposition (c : Certificate ι) :
    c.parent = c.removed ⊔ c.residual := by
  simpa [parent, removed, residual] using
    (BinaryTransvection.orthogonal_pair_decomp c.source c.target
      c.source_unit c.source_target_orthogonal)

theorem removed_le_parent (c : Certificate ι) :
    c.removed ≤ c.parent := by
  rw [decomposition c]
  exact le_sup_left

end Certificate

open TensorFrameLabels

def ofPure3 {h : ℕ}
    (a b c a' b' c' : Fin h → ZMod 2)
    (ha : dotProduct a a = (1 : ZMod 2))
    (hb : dotProduct b b = (1 : ZMod 2))
    (hc : dotProduct c c = (1 : ZMod 2))
    (horth : dotProduct a a' = (0 : ZMod 2)) :
    Certificate (Fin h × (Fin h × Fin h)) where
  source := pure3 a b c
  target := pure3 a' b' c'
  source_unit := pure3_norm_of_unit a b c ha hb hc
  source_target_orthogonal := pure3_orthogonal_of_first a b c a' b' c' horth

theorem ofPure3_decomposition {h : ℕ}
    (a b c a' b' c' : Fin h → ZMod 2)
    (ha : dotProduct a a = (1 : ZMod 2))
    (hb : dotProduct b b = (1 : ZMod 2))
    (hc : dotProduct c c = (1 : ZMod 2))
    (horth : dotProduct a a' = (0 : ZMod 2)) :
    (ofPure3 a b c a' b' c' ha hb hc horth).parent =
      (ofPure3 a b c a' b' c' ha hb hc horth).removed ⊔
        (ofPure3 a b c a' b' c' ha hb hc horth).residual := by
  exact Certificate.decomposition _

theorem pure3_removed_le_parent {h : ℕ}
    (a b c a' b' c' : Fin h → ZMod 2)
    (horth : dotProduct a a' = (0 : ZMod 2)) :
    (ZMod 2) ∙ pure3 a b c ≤
      ((ZMod 2) ∙ pure3 a' b' c').orthogonalBilin
        (tensorDotForm : _) := by
  exact pure3_line_nested_of_first_orth a b c a' b' c' horth

end StageResidual
end ExactFourier
end OAI
