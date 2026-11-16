module

public import QuantitativeMaassFullFiniteNormalizationV1
public import QuantitativeHolomorphicNewtonTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticSectorSigns QuantitativeHolomorphic AsymptoticFiniteBranch
open AsymptoticCylinderLift
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Exact ambient realization of the weight-zero finite reconstruction.
Both endpoint restrictions are already present in the finite branch list. -/
theorem fullExpression_eq_ambient (e : Sector N) (j J : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    holomorphicSum (fullExpression A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J)) 0=
      lift.toContinuousLinearMap.comp ((finiteReconstruction A hN P e j J).comp
        (AsymptoticCylinderTerminal.ambientLift P'.ε).adjoint) := by
  intro P'
  let E := holomorphicSum (fullExpression A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J)) 0
  let S := AsymptoticCylinderTerminal.ambientLift P'.ε
  have he : lift.toContinuousLinearMap.adjoint.comp (E.comp S)=
      finiteReconstruction A hN P e j J :=
    cylinder_fullExpression A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J) 0
  have hl : stripProjection.comp E=E :=
    holomorphicSum_full_left_strip A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J) 0
  have hr : E.comp (AsymptoticCertificateOperators.highProjection A P')=E :=
    holomorphicSum_full_right_terminal A hN P' (multiplier e) j (Finset.Icc (-(J:ℤ)) J) 0
  have ht : S.comp S.adjoint=AsymptoticCertificateOperators.highProjection A P' :=
    AsymptoticCylinderTerminal.ambientLift_self_adjoint P'.ε
  rw [←he]
  change E=lift.toContinuousLinearMap.comp
    ((lift.toContinuousLinearMap.adjoint.comp (E.comp S)).comp S.adjoint)
  rw [←comp_assoc,←comp_assoc,lift_comp_adjoint,←comp_assoc]
  change E=((stripProjection.comp E).comp S).comp S.adjoint
  rw [hl,comp_assoc,ht,hr]

def scaledFullExpression (e : Sector N) (j J : ℕ) : Expression :=
  scaleExpression ((countReconstructionBound A P)⁻¹ : ℝ)
    (fullExpression A hN (AsymptoticReconstructedCount.parameters A P)
      (multiplier e) j (Finset.Icc (-(J:ℤ)) J))

theorem scaledFullExpression_eq_ambient (e : Sector N) (j J : ℕ) :
    holomorphicSum (scaledFullExpression A hN P e j J) 0=
      lift.toContinuousLinearMap.comp
        (((countReconstructionBound A P)⁻¹ • finiteReconstruction A hN P e j J).comp
          (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  rw [scaledFullExpression,holomorphicSum_scale,fullExpression_eq_ambient,smul_comp,comp_smul]
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (countReconstructionBound A P)⁻¹
    (lift.toContinuousLinearMap.comp ((finiteReconstruction A hN P e j J).comp
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint))).symm

/-- Newton normalization is realized by the same finite rational branches.
No Fourier-mode projection occurs in the polynomial. -/
theorem normalizedFullExpression_eq_ambient (e : Sector N) (n j J : ℕ) :
    holomorphicSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) 0=
      lift.toContinuousLinearMap.comp ((finiteNormalizedReconstruction A hN P e n j J).comp
        (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  rw [holomorphicSum_normalizedReconstructionExpression,scaledFullExpression_eq_ambient]
  exact polynomialNormalizedReconstruction_transport _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) _ lift.adjoint_comp_self _ n

#print axioms fullExpression_eq_ambient
#print axioms scaledFullExpression_eq_ambient
#print axioms normalizedFullExpression_eq_ambient
end QuantitativeMaass.EulerHilbert.FullTerminal
