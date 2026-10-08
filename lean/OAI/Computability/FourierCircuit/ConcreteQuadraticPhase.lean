import OAI.Computability.FourierCircuit.QuadraticPhaseData

/-!
# A concrete one-coordinate projected phase

This file instantiates the projected-phase interface on the span of one
coordinate vector.  It is a small but genuine nondegenerate example: the
projection is the orthogonal projection onto `F₂ · e_w`, with kernel the
coordinate hyperplane.  It is deliberately a local construction; it does not
claim the nested family or the all-length Fourier schedule from the paper.
-/

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

open AddressPhaseConjugation
open BinaryTransvection

abbrev F2 := BinaryAddressPermutation.F2
abbrev Address (ι : Type) := BinaryAddressPermutation.Address ι

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateProjection (w : ι) :
    Address ι →ₗ[F2] Address ι :=
  (coordinateEval w).smulRight (coordinate w)

theorem coordinateProjection_apply (w : ι) (x : Address ι) :
    coordinateProjection w x = x w • coordinate w := by
  change x w • coordinate w = x w • coordinate w
  rfl

def coordinateLine (w : ι) : Submodule F2 (Address ι) :=
  F2 ∙ coordinate w

theorem coordinateProjection_mem_line (w : ι) (x : Address ι) :
    coordinateProjection w x ∈ coordinateLine w := by
  rw [coordinateProjection_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem coordinateProjection_fixed_line (w : ι)
    {u : Address ι} (hu : u ∈ coordinateLine w) :
    coordinateProjection w u = u := by
  rcases Submodule.mem_span_singleton.mp hu with ⟨a, rfl⟩
  simp [coordinateProjection_apply, coordinate, coordinateEval,
    smul_eq_mul]

theorem coordinateLine_orthogonal (w : ι) :
    (coordinateLine w).orthogonalBilin
      (BinaryTransvection.bilinearDot : _ ) =
      LinearMap.ker (coordinateEval w) := by
  change (F2 ∙ coordinate w).orthogonalBilin
      (BinaryTransvection.bilinearDot : _ ) =
      LinearMap.ker (coordinateEval w)
  rw [Submodule.orthogonalBilin_span_singleton]
  apply congrArg LinearMap.ker
  apply LinearMap.ext
  intro x
  change dotProduct (coordinate w) x = x w
  exact coordinate_dot w x

theorem coordinateProjection_kernel (w : ι) :
    LinearMap.ker (coordinateProjection w) =
      (coordinateLine w).orthogonalBilin
        (BinaryTransvection.bilinearDot : _ ) := by
  rw [coordinateLine_orthogonal]
  ext x
  constructor
  · intro hx
    have hx' : x w • coordinate w = 0 := by
      simpa [coordinateProjection_apply] using hx
    have hcoord : coordinate w ≠ (0 : Address ι) := by
      intro h
      have := congrFun h w
      simpa [coordinate] using this
    have : x w = 0 := by
      exact smul_eq_zero.mp hx' |>.resolve_right hcoord
    exact this
  · intro hx
    simp only [LinearMap.mem_ker, coordinateProjection_apply]
    rw [smul_eq_zero]
    exact Or.inl hx

end ConcreteQuadraticPhase
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

/-- Hamming weight of a binary address, represented by the cardinality of its
one-coordinate subtype. -/
noncomputable def binaryWeight (x : Address ι) : ℕ :=
  Fintype.card {i : ι // x i = (1 : F2)}

/-- A fully populated `QuadraticPhaseData` toy instance for the coordinate
line.  It satisfies the interface's nondegenerate-kernel condition; it is not
the nested family or global schedule from the paper. -/
noncomputable def coordinateQuadraticPhaseData (w : ι) :
    QuadraticPhaseData ι :=
  { U := coordinateLine w
    projection := coordinateProjection w
    projection_mem := coordinateProjection_mem_line w
    projection_fixed := coordinateProjection_fixed_line w
    projection_kernel := coordinateProjection_kernel w
    weight := binaryWeight
    q := fun x => Complex.I ^ binaryWeight (coordinateProjection w x)
    q_eq := by intro x; rfl }

@[simp] theorem coordinateQuadraticPhaseData_q
    (w : ι) (x : Address ι) :
    (coordinateQuadraticPhaseData w).q x =
      Complex.I ^ binaryWeight (coordinateProjection w x) := by
  rfl

end ConcreteQuadraticPhase
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

@[simp] theorem binaryWeight_zero (w : ι) : binaryWeight (0 : Address ι) = 0 := by
  classical
  simp [binaryWeight]

@[simp] theorem binaryWeight_coordinate (w : ι) : binaryWeight (coordinate w) = 1 := by
  classical
  simp [binaryWeight, coordinate]

theorem binaryWeight_coordinateProjection (w : ι) (x : Address ι) :
    binaryWeight (coordinateProjection w x) = if x w = 0 then 0 else 1 := by
  classical
  rw [coordinateProjection_apply]
  by_cases hx : x w = 0
  · simp [hx, binaryWeight]
  · have hx1 : x w = (1 : F2) := by
      have hvals : x w = (0 : F2) ∨ x w = (1 : F2) := by
        have hv : (x w).val = 0 ∨ (x w).val = 1 := by
          have hlt : (x w).val < 2 := ZMod.val_lt (x w)
          omega
        rcases hv with hv | hv
        · exact Or.inl ((ZMod.val_eq_zero (x w)).mp hv)
        · right
          apply ZMod.val_injective 2
          exact hv
      exact hvals.resolve_left hx
    rw [hx1]
    simp [binaryWeight, coordinate]

end ConcreteQuadraticPhase
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

@[simp] theorem coordinateQuadraticPhaseData_q_eq_one_or_I
    (w : ι) (x : Address ι) :
    (coordinateQuadraticPhaseData w).q x =
      if x w = 0 then 1 else Complex.I := by
  rw [coordinateQuadraticPhaseData_q, binaryWeight_coordinateProjection]
  split <;> simp_all

end ConcreteQuadraticPhase
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

/-- The coordinate line and its orthogonal complement split every binary
address. -/
theorem coordinateLine_sup_orthogonal_eq_top (w : ι) :
    coordinateLine w ⊔
        (coordinateLine w).orthogonalBilin
          (BinaryTransvection.bilinearDot : _) = ⊤ := by
  rw [coordinateLine_orthogonal]
  apply top_unique
  intro x hx
  let a : F2 := x w
  let r : Address ι := x + a • coordinate w
  have hr : r ∈ LinearMap.ker (coordinateEval w) := by
    rw [LinearMap.mem_ker]
    dsimp [r, a]
    simp [coordinateEval, coordinate]
  have ha : a • coordinate w ∈ coordinateLine w :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hr' : r ∈ (coordinateLine w).orthogonalBilin
      (BinaryTransvection.bilinearDot : _) := by
    rw [coordinateLine_orthogonal]
    exact hr
  have hdecomp : x = a • coordinate w + r := by
    dsimp [r]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinate]
    rw [add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hdecomp]
  exact Submodule.mem_sup.mpr ⟨a • coordinate w, ha, r, hr', rfl⟩

/-- The coordinate line meets its orthogonal complement trivially. -/
theorem coordinateLine_inf_orthogonal_eq_bot (w : ι) :
    coordinateLine w ⊓
        (coordinateLine w).orthogonalBilin
          (BinaryTransvection.bilinearDot : _) = ⊥ := by
  rw [coordinateLine_orthogonal]
  apply le_antisymm
  · intro z hz
    rcases Submodule.mem_inf.mp hz with ⟨hzline, hzker⟩
    rcases Submodule.mem_span_singleton.mp hzline with ⟨a, ha⟩
    rw [Submodule.mem_bot]
    apply_fun fun v => v w at ha
    have hzero : (coordinateEval w) z = 0 := by
      exact LinearMap.mem_ker.mp hzker
    have hcoord : z w = 0 := by
      exact hzero
    have hzzero : z = 0 := by
      rw [ha]
      ext i
      simp only [Pi.smul_apply, coordinate]
      by_cases hi : i = w
      · subst i
        simp [hcoord]
      · simp [hi]
    exact hzzero
  · exact bot_le

end ConcreteQuadraticPhase
end ExactFourier
end OAI

namespace OAI
namespace ExactFourier
namespace ConcreteQuadraticPhase

@[simp] theorem coordinateProjection_idem (w : ι) (x : Address ι) :
    coordinateProjection w (coordinateProjection w x) =
      coordinateProjection w x := by
  rw [coordinateProjection_apply, coordinateProjection_apply]
  simp [coordinate, smul_eq_mul]

end ConcreteQuadraticPhase
end ExactFourier
end OAI
