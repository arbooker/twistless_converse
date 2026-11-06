module

public import QuantitativeEulerEndpointUnitSubcornerV1
public import QuantitativeEulerEndpointTerminalAlgebraV1
public import QuantitativeEulerEndpointSubcornerMassV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight
open QuantitativeEulerEndpointRegularBase AsymptoticRegularTrace
open QuantitativeEulerEndpointUnitSubcorner QuantitativeEulerEndpointCanonicalHalf
open AsymptoticRegularReconstruction AsymptoticSubgroupSupport MeasureTheory

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
local notation "s" => terminalRegion A P
local notation "hs" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable s hs

def terminalSpace (x : Base) : ClosedSubmodule ℂ AsymptoticFiniteBranch.RegularSpace where
  toSubmodule := TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x))).isClosed

theorem terminal_space_projection (x : Base) :
    (terminalSpace A P x).toSubmodule.starProjection=rep A P 1 x := (rep_one A P x).symm

def half (F : Algebra A P) : UpperHalfPlane → ClosedSubmodule ℂ AsymptoticFiniteBranch.RegularSpace :=
  fun x => space action_measurable s hs 1 hp (lift action_measurable s hs F) (show Base from x)

def halfProjection (F : Algebra A P) (hF : IsSelfAdjoint F) : Algebra A P :=
  projection action_measurable s hs 1 hp (terminalSpace A P) (terminal_space_projection A P)
    (lift action_measurable s hs F)
    (by apply Subtype.ext; exact hF)

theorem half_projection (F : Algebra A P) (hF : IsSelfAdjoint F) : IsStarProjection (halfProjection A P F hF) :=
  projection_isStarProjection action_measurable s hs 1 hp (terminalSpace A P)
    (terminal_space_projection A P) _ _

theorem half_representation (F : Algebra A P) (hF : IsSelfAdjoint F) (x : Base) :
    rep A P (halfProjection A P F hF) x=(half A P F x).toSubmodule.starProjection := rfl

theorem half_regular (F : Algebra A P) (hF : IsSelfAdjoint F) :
    (∀ g k,Measurable (fun x : UpperHalfPlane => matrix (half A P F x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (half A P F x).toSubmodule.starProjection) := by
  exact ⟨QuantitativeSpectralRegularAlgebra.representation_matrix_measurable
    _ _ action_measurable s hs (halfProjection A P F hF),
    QuantitativeSpectralRegularAlgebra.representation_covariant
    _ _ action_measurable s hs (halfProjection A P F hF)⟩

theorem half_le_terminal (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) (x : UpperHalfPlane) :
    (half A P F x).toSubmodule≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x := by
  apply space_le_baseline action_measurable s hs 1 hp (lift action_measurable s hs F)
    (lift_nonneg action_measurable s hs F hF0) (terminalSpace A P) _ x
  intro y
  rw [terminal_space_projection]
  exact (QuantitativeSpectralRegularOrder.pointwise_le_iff action_measurable s hs F 1).mpr hF1 y

theorem half_supported (F : Algebra A P) (hF : IsSelfAdjoint F)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hFS : ∀ x,Supported S (rep A P F x)) (x : UpperHalfPlane) :
    Supported S (half A P F x).toSubmodule.starProjection := by
  apply QuantitativeSpectralCutRegularity.highAt_supported S (rep A P F x) (hFS x)
  have hF' : IsSelfAdjoint (lift action_measurable s hs F) := by
    apply Subtype.ext
    exact hF
  exact hF'.map (QuantitativeEulerEndpointCornerCut.evaluation action_measurable s hs 1 hp x)

theorem half_mass (F : Algebra A P) (hF : IsSelfAdjoint F) :
    tr A P (halfProjection A P F hF)=QuantitativeEulerEndpointPrepared.cornerMass (half A P F) :=
  QuantitativeEulerEndpointSubcornerMass.initial_trace_eq action_measurable s hs
    (halfProjection A P F hF) (half_projection A P F hF) measure (terminal_finite A P)

#print axioms half_projection
#print axioms half_regular
#print axioms half_le_terminal
#print axioms half_supported
#print axioms half_mass
end QuantitativeEulerEndpointTerminalAlgebra
