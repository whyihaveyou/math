import OAI.Computability.FourierCircuit.FusedFrameLocalCertificate
import OAI.Computability.FourierCircuit.CenterBoundaryShearScheduleAudit

/-!
# Naturality and array restoration for the fused centre rows

This file supplies a concrete scalar commutation statement, rather than a
structure whose premise is the desired commutation.  Four intertwining laws
for `R`, `G`, `J`, and `V` suffice for the six fused rows to commute with a
change of scalar banks.  A common address permutation on every bank is an
unconditional instance: the scalar maps act pointwise in that address.

For the tensor-lifted binary shear, we bind this pointwise round trip to the
existing local target-boundary certificate.  Both auxiliary banks may start
arbitrarily and are restored exactly, after transporting back.  This does
not prove that the paper's framed gates act pointwise on these same arrays,
that a *selective* transport of only the centre bank commutes with the rows,
or that the old boundary stays fixed during a common address permutation.
The latter is precisely the covariance obstruction audited elsewhere.  A
physical realization still has to justify that connection and its schedule.

The h=24 comparison at the end is conditional direction accounting only.
Its normalized saving is not a recurrence exponent.
-/

namespace OAI
namespace ExactFourier
namespace FusedCentreTransportNaturality

open CompressedInvocation FusedCentreInvocation

section Naturality

variable {X A C X' A' C' : Type*}
  [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]
  [AddCommGroup X'] [AddCommGroup A'] [AddCommGroup C']

/-- Change all four scalar registers using the specified bank maps. -/
def mapState (eX : X →+ X') (eA : A →+ A') (eC : C →+ C')
    (s : State X A C) : State X' A' C' :=
  ⟨eX s.x, eX s.y, eA s.side, eC s.center⟩

/-- A row-by-row sufficient compatibility interface.  In particular, these
conditions concern the primitive maps, not the final fused update. -/
theorem fusedRows_natural
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (R' : C' →+ X') (G' : X' → C') (J' : A' →+ X') (V' : X' → A')
    (eX : X →+ X') (eA : A →+ A') (eC : C →+ C')
    (hR : ∀ c, eX (R c) = R' (eC c))
    (hG : ∀ x, eC (G x) = G' (eX x))
    (hJ : ∀ a, eX (J a) = J' (eA a))
    (hV : ∀ x, eA (V x) = V' (eX x))
    (s : State X A C) :
    mapState eX eA eC (fusedRows R G J V s) =
      fusedRows R' G' J' V' (mapState eX eA eC s) := by
  cases s
  simp [mapState, fusedRows, map_add, map_sub, hR, hG, hJ, hV]

/-- The same primitive conditions also intertwine the reversed six rows. -/
theorem inverseFusedRows_natural
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (R' : C' →+ X') (G' : X' → C') (J' : A' →+ X') (V' : X' → A')
    (eX : X →+ X') (eA : A →+ A') (eC : C →+ C')
    (hR : ∀ c, eX (R c) = R' (eC c))
    (hG : ∀ x, eC (G x) = G' (eX x))
    (hJ : ∀ a, eX (J a) = J' (eA a))
    (hV : ∀ x, eA (V x) = V' (eX x))
    (s : State X A C) :
    mapState eX eA eC (inverseFusedRows R G J V s) =
      inverseFusedRows R' G' J' V' (mapState eX eA eC s) := by
  cases s
  simp [mapState, inverseFusedRows, map_add, map_sub, hR, hG, hJ, hV]

end Naturality

section Arrays

variable {Q X A C : Type*}
  [AddCommGroup X] [AddCommGroup A] [AddCommGroup C]

/-- Move the state stored at address `q` to `e q`, uniformly for all banks. -/
def transport (e : Q ≃ Q) (s : Q → State X A C) : Q → State X A C :=
  fun q => s (e.symm q)

@[simp] theorem transport_at_image (e : Q ≃ Q) (s : Q → State X A C)
    (q : Q) : transport e s (e q) = s q := by
  simp [transport]

/-- The six rows applied independently to every address. -/
def fusedPointwise (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (s : Q → State X A C) : Q → State X A C :=
  fun q => fusedRows R G J V (s q)

/-- Common address transport commutes with the actual six-row expression,
even without the scalar identity needed to implement a source shear. -/
theorem fusedPointwise_transport
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (e : Q ≃ Q) (s : Q → State X A C) :
    fusedPointwise R G J V (transport e s) =
      transport e (fusedPointwise R G J V s) := by
  rfl

/-- Restore the address frame after the fused rows.  This equality includes
arbitrary initial values of both auxiliary banks at every address. -/
theorem transport_fused_roundtrip
    (R : C →+ X) (G : X → C) (J : A →+ X) (V : X → A)
    (hidentity : ∀ x, R (G x) + J (V x) = x)
    (e : Q ≃ Q) (s : Q → State X A C) :
    transport e.symm (fusedPointwise R G J V (transport e s)) =
      fun q => {s q with y := (s q).y + (s q).x} := by
  funext q
  simp [transport, fusedPointwise, fusedRows_restore R G J V hidentity]

end Arrays

section LocalBridge

open CenterBoundaryTensorLift BinaryTransvection CenterFramedInvocation

variable {ι : Type*} [Fintype ι] {h : ℕ}
variable {K : Type*} [Field K] [CharZero K]

/-- The address equivalence fixed by the same local frame witness used for
the readout membership theorem. -/
noncomputable def localAddressTransport
    (d : FusedFrameLocalCertificate.Data (ι := ι) (h := h) (K := K)) :
    CenterBoundaryTensorLift.Address ι h ≃ CenterBoundaryTensorLift.Address ι h :=
  (CenterBoundaryTensorLift.lift
    (unitCoordinateEquiv d.framed.frame.target d.witness
      d.framed.frame.target_unit d.witness_zero)).toEquiv

/-- Binding of scalar restoration and the sheared line to a single local
transport.  The array round trip is unconditional for this pointwise model;
no gate cost, selective-bank realization, or global DAG is asserted. -/
theorem local_transport_restore_and_readout
    (d : FusedFrameLocalCertificate.Data (ι := ι) (h := h) (K := K))
    (s : CenterBoundaryTensorLift.Address ι h → ScalarState h K) :
    transport (localAddressTransport d).symm
        (fusedPointwise OrderedPairs.RHom
          CenterCompression.compressedG OrderedPairs.JHom
          OrderedPairs.V
          (transport (localAddressTransport d) s)) =
      (fun q => {s q with y := (s q).y + (s q).x}) ∧
    d.source_row + localAddressTransport d
        (CenterRowGeneral.insert d.pre d.framed.frame.target) ∈
      SideRowGeneralArbitrary.L5 d.pre d.framed.frame.target := by
  constructor
  · exact transport_fused_roundtrip _ _ _ _
      CompressedInvocation.OrderedPairs.identity (localAddressTransport d) s
  · exact FusedFrameLocalCertificate.lifted_readout_legal d

/-- Explicit auxiliary-bank restoration extracted from the same certificate.
The returned state at each address has its original side and centre data. -/
theorem local_transport_auxiliary_banks_restored
    (d : FusedFrameLocalCertificate.Data (ι := ι) (h := h) (K := K))
    (s : CenterBoundaryTensorLift.Address ι h → ScalarState h K)
    (q : CenterBoundaryTensorLift.Address ι h) :
    let returned := transport (localAddressTransport d).symm
      (fusedPointwise OrderedPairs.RHom
        CenterCompression.compressedG OrderedPairs.JHom
        OrderedPairs.V
        (transport (localAddressTransport d) s))
    (returned q).side = (s q).side ∧ (returned q).center = (s q).center := by
  dsimp only
  rw [(local_transport_restore_and_readout d s).1]
  exact ⟨rfl, rfl⟩

end LocalBridge

namespace H24

/-- Charging all six nominal transport phases still retains over three
quarters of the uncharged fused saving.  This is an integer ledger, with
the nominal event model inherited from `CenterBoundaryShearScheduleAudit`. -/
theorem six_phase_retains_three_quarters :
    3 * CenterBoundaryShearCandidate.H24.centreFusionSaving <
      4 * (CenterBoundaryShearCandidate.H24.centreFusionSaving -
        (6 * (CenterBoundaryShearScheduleAudit.H24.I *
          CenterBoundaryShearScheduleAudit.H24.h) : ℤ)) := by
  have hp := CenterBoundaryShearScheduleAudit.H24.directional_price_eq
  have hph :
      (CenterBoundaryShearScheduleAudit.H24.I : ℤ) *
          CenterBoundaryShearScheduleAudit.H24.h = 294953472 := by
    exact_mod_cast hp
  norm_num [CenterBoundaryShearCandidate.H24.centreFusionSaving_eq,
    hph]

/-- The six-phase conditional normalized saving is more than twice the
earlier compressed-centre ledger; neither side is itself an exponent. -/
theorem six_phase_exceeds_twice_compressed_normalized :
    2 * CenterCompression.H24.epsilonCompressed <
      CenterBoundaryShearScheduleAudit.H24.sixPhaseNormalized := by
  rw [CenterCompression.H24.epsilonCompressed_eq,
    CenterBoundaryShearScheduleAudit.H24.sixPhaseNormalized_eq]
  norm_num

end H24
end FusedCentreTransportNaturality
end ExactFourier
end OAI
