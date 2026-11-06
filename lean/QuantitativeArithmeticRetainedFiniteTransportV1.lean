module

public import QuantitativeArithmeticRetainedFiniteSupportV1
public import QuantitativeArithmeticRetainedFiniteNormalizationV1
public import QuantitativeHolomorphicNewtonTransportV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFiniteTransport
open UpperHalfPlane ContinuousLinearMap AsymptoticFiniteBranch AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeArithmeticRetainedFiniteSchedule (expression)
open QuantitativeHolomorphic
open AsymptoticCylinderLift
open AsymptoticHyperbolicSlash (Space)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)
    (hS : ∀p∈S,p.Prime) (hN : 0<N)

/-- The original mixed finite expression is exactly the transported cylinder
operator; both its source and target supports are proved from its branches. -/
theorem full_eq_cylinder (δ : ℝ) (e : Sector N) (m : ℕ) :
    holomorphicSum (expression A P hS hN δ e) m=
      lift.toContinuousLinearMap.comp ((cylinderFinite A P hS hN δ e m).comp
        (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint) := by
  let R := holomorphicSum (expression A P hS hN δ e) m
  let S := AsymptoticCylinderTerminal.ambientLift P.ε
  have hl : stripProjection.comp R=R :=
    QuantitativeArithmeticRetainedFiniteExpressions.full_left_strip A hS hN P _ _ _ _ _ m
  have hr : R.comp (QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P)=R :=
    QuantitativeArithmeticRetainedFiniteExpressions.full_right_terminal A hS hN P _ _ _ _ _ m
  have hs : S.comp S.adjoint=QuantitativeArithmeticRetainedAnalyticReconstruction.highProjection A P :=
    AsymptoticCylinderTerminal.ambientLift_self_adjoint P.ε
  have hc : cylinderFinite A P hS hN δ e m=lift.toContinuousLinearMap.adjoint.comp (R.comp S) := rfl
  rw [hc]
  calc
    R = R.comp (S.comp S.adjoint) := by rw [hs,hr]
    _ = (stripProjection.comp R).comp (S.comp S.adjoint) := by rw [hl]
    _ = _ := by rw [stripProjection,←lift_comp_adjoint]; simp only [comp_assoc]; rfl

def scaledExpression (δ Y : ℝ) (e : Sector N) : Expression :=
  scaleExpression ((bound A P)⁻¹:ℝ)
    (composeExpression [heightCorner Y]
      (composeExpression [weight P.epsilon_pos] (expression A P hS hN δ e)))

theorem physical_scaled (δ Y : ℝ) (e : Sector N) (m : ℕ) :
    holomorphicSum (scaledExpression A P hS hN δ Y e) m=
      lift.toContinuousLinearMap.comp ((physicalScaled A P hS hN δ Y e m).comp
        (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint) := by
  rw [scaledExpression,holomorphicSum_scale,holomorphicSum_compose,holomorphicSum_compose]
  simp only [holomorphicSum_singleton]
  rw [full_eq_cylinder]
  ext1 f
  simp only [comp_apply,smul_apply,physicalScaled,map_smul_of_tower]
  have ht := lift_heightCorner Y m (AsymptoticCylinder.inclusion P.epsilon_pos
    (cylinderFinite A P hS hN δ e m ((AsymptoticCylinderTerminal.ambientLift P.ε).adjoint f)))
  rw [lift_inclusion] at ht
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _).symm.trans
    (congrArg (fun v : Space => (bound A P)⁻¹ • v) ht.symm)

theorem regular_full_eq (δ : ℝ) (e : Sector N) (z : ℍ) :
    regularSum (expression A P hS hN δ e) z=
      (regularFinite A P hS hN δ e z).comp
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint := by
  let R := regularSum (expression A P hS hN δ e) z
  let S := (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
  have hs : S.comp S.adjoint=QuantitativeArithmeticRetainedRegularExtension.highProjection A P z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint _ z
  have hr : R.comp (QuantitativeArithmeticRetainedRegularExtension.highProjection A P z)=R :=
    QuantitativeArithmeticRetainedFiniteExpressions.regular_full_right_terminal A hS hN P _ _ _ _ _ z
  change R=(R.comp S).comp S.adjoint
  rw [comp_assoc,hs,hr]

theorem regular_scaled (δ Y : ℝ) (e : Sector N) (z : ℍ) :
    regularSum (scaledExpression A P hS hN δ Y e) z=
      (regularScaled A P hS hN δ Y e z).comp
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint := by
  have hb (b : Branch) : regularSum [b] z=regular b z := add_zero _
  have hr : regularSum (scaledExpression A P hS hN δ Y e) z=
      (((bound A P)⁻¹:ℝ):ℂ) • (AsymptoticRegularHeightCutoff.projection Y z).comp
        ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp
          (regularSum (expression A P hS hN δ e) z)) := by
    unfold scaledExpression
    rw [regularSum_scale,regularSum_compose,regularSum_compose,hb,hb,regular_weight,heightCorner,regular_corner]
    rfl
  apply hr.trans
  have hf := congrArg (fun R : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space =>
    (((bound A P)⁻¹:ℝ):ℂ) • (AsymptoticRegularHeightCutoff.projection Y z).comp
      ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp R))
    (regular_full_eq A P hS hN δ e z)
  apply hf.trans
  ext1 f
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (bound A P)⁻¹
    ((AsymptoticRegularHeightCutoff.projection Y z)
      ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z)
        ((regularFinite A P hS hN δ e z)
          ((QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint f))))).symm

def normalizedExpression (τ : ℝ) (e : Sector N) : Expression :=
  normalizedReconstructionExpression
    (scaledExpression A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e) (newtonDepth A P τ)

theorem physical_normalized (τ : ℝ) (e : Sector N) (m : ℕ) :
    holomorphicSum (normalizedExpression A P hS hN τ e) m=
      lift.toContinuousLinearMap.comp ((polynomialNormalizedReconstruction
        (physicalScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e m)
        (newtonDepth A P τ)).comp (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint) := by
  rw [normalizedExpression,holomorphicSum_normalizedReconstructionExpression,physical_scaled]
  exact polynomialNormalizedReconstruction_transport _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) _ lift.adjoint_comp_self _ _

theorem regular_normalized (τ : ℝ) (e : Sector N) (z : ℍ) :
    regularSum (normalizedExpression A P hS hN τ e) z=
      (polynomialNormalizedReconstruction
        (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z)
        (newtonDepth A P τ)).comp
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint := by
  have ht := polynomialNormalizedReconstruction_transport
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
    (AsymptoticOrbitRegion.adjoint_comp_subtype _ z)
    (1:AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1:AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ)
  have hh := (by simpa only [one_def,id_comp] using ht)
  exact (regularSum_normalizedReconstructionExpression _ _ z).trans
    ((congrArg (fun R : AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space =>
      polynomialNormalizedReconstruction R (newtonDepth A P τ))
      (regular_scaled A P hS hN _ _ e z)).trans hh)

/-- The common finite expression approximates the original normalized
reconstruction on the entire physical ambient Hilbert space. -/
theorem physical_ambient_error {τ : ℝ} (hτ : 0<τ) (e : Sector N) (m : ℕ) :
    ‖holomorphicSum (normalizedExpression A P hS hN τ e) m-
      lift.toContinuousLinearMap.comp
        ((QuantitativeArithmeticRetainedCylinderNormalization.normalized A hS hN P
          (multiplier e) (QuantitativeArithmeticRetainedSectorReconstruction.ramifiedParameter e)
          (by omega : 2≤exponent A P+3) m).comp
          (AsymptoticCylinderTerminal.ambientLift P.ε).adjoint)‖≤τ := by
  rw [physical_normalized]
  exact (norm_isometric_transport_difference_le _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) _ lift.adjoint_comp_self _ _).trans
    (scheduled_physical_error A P hS hN hτ e m)

/-- The identical expression has the identical error bound in every regular
orbit representation, with no extra spectral hypotheses. -/
theorem regular_ambient_error {τ : ℝ} (hτ : 0<τ) (e : Sector N) (z : ℍ) :
    ‖regularSum (normalizedExpression A P hS hN τ e) z-
      (QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
        (multiplier e) (QuantitativeArithmeticRetainedSectorReconstruction.ramifiedParameter e)
        (by omega : 2≤exponent A P+3) z).comp
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL.adjoint‖≤τ := by
  have he := norm_isometric_transport_difference_le
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).subtypeL
    (AsymptoticOrbitRegion.adjoint_comp_subtype _ z)
    (1:AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1:AsymptoticRegularFoldedLow.Space →L[ℂ] AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (polynomialNormalizedReconstruction
      (regularScaled A P hS hN (rawTolerance A P τ) (lowerHeight A P τ) e z) (newtonDepth A P τ))
    (QuantitativeArithmeticRetainedRegularNormalization.normalized A hS hN P
      (multiplier e) (QuantitativeArithmeticRetainedSectorReconstruction.ramifiedParameter e)
      (by omega : 2≤exponent A P+3) z)
  have hh := he.trans (scheduled_regular_error A P hS hN hτ e z)
  simpa only [one_def,id_comp,regular_normalized] using hh

#print axioms physical_ambient_error
#print axioms regular_ambient_error
#print axioms full_eq_cylinder
#print axioms physical_scaled
#print axioms regular_scaled
end QuantitativeArithmeticRetainedFiniteTransport
