module

public import QuantitativeEulerEndpointApproximateSectorTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace QuantitativeHolomorphic
open QuantitativeEulerEndpointSector
open scoped InnerProduct
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def terminalCompression (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :=
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  S.adjoint.comp (F.comp S)

theorem ambient_sector_residual (hN : 0<N) (h : ℕ) (e : Sector N)
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) (δ : ℝ)
    (herr : ‖F*normalizedPhysicalSectorProjection A P hN h e-normalizedPhysicalSectorProjection A P hN h e‖≤δ)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    ‖terminalCompression A P F (normalizedSectorCoordinates A hN P h e a)-normalizedSectorCoordinates A hN P h e a‖≤
      δ*‖normalizedSectorCoordinates A hN P h e a‖ := by
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  let v := normalizedSectorCoordinates A hN P h e a
  let E := normalizedPhysicalSectorProjection A P hN h e
  have hiso : ∀ v,‖S v‖=‖v‖ := (norm_map_iff_adjoint_comp_self S).mpr
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hSn : ‖S.adjoint‖≤1 := by
    rw [adjoint.norm_map]
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [hiso,one_mul]
  have hSv : S.adjoint (S v)=v := congrArg (fun T => T v)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hEv : E (S v)=S v := by
    let _ := normalizedPhysicalSector_finiteDimensional A P hN h e
    exact (LinearMap.range (normalizedPhysicalSectorMap A P hN h e)).starProjection_eq_self_iff.mpr ⟨a,rfl⟩
  have he : (F*E-E) (S v)=F (S v)-S v := by
    change F (E (S v))-E (S v)=_
    rw [hEv]
  calc
    ‖terminalCompression A P F v-v‖=‖S.adjoint ((F*E-E) (S v))‖ := by
      rw [he,map_sub,hSv]
      rfl
    _ ≤ ‖(F*E-E) (S v)‖ := (S.adjoint.le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSn (norm_nonneg _))
    _ ≤ ‖F*E-E‖*‖S v‖ := (F*E-E).le_opNorm _
    _ ≤ δ*‖S v‖ := mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = δ*‖v‖ := by rw [hiso]

/-- Actual ambient sector preservation yields an actual summable weighted
holomorphic trace bound for the original coefficient-sector dimension. -/
theorem ambient_sector_finrank_mul_le_trace (hN : 0<N) (h : ℕ) (e : Sector N)
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) (hF : 0≤F) (δ : ℝ)
    (herr : ‖F*normalizedPhysicalSectorProjection A P hN h e-normalizedPhysicalSectorProjection A P hN h e‖≤δ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      trace fb (AsymptoticObservation.compressedSandwich (normalizedCountReconstruction A hN P h e) (terminalCompression A P F) W) := by
  refine sector_finrank_mul_le_trace A hN P h e (terminalCompression A P F) ?_ δ ?_
  · exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hF).adjoint_conj
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε))
  · exact ambient_sector_residual A P hN h e F δ herr

#print axioms ambient_sector_residual
#print axioms ambient_sector_finrank_mul_le_trace
end QuantitativeEulerEndpointApproximateTrace

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointApproximateTrace
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticDiagonalTrace
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_sector_trace (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let V := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let F := holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      trace fb (AsymptoticObservation.compressedSandwich (normalizedCountReconstruction A (NeZero.pos N) P h e) (terminalCompression A P F) V) := by
  apply ambient_sector_finrank_mul_le_trace A P (NeZero.pos N) h e
  · exact (actualFiniteExpression_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq).1
  · exact actualFiniteExpression_sector_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h hK q hq hbudget

#print axioms actualFiniteExpression_sector_trace
end QuantitativeEulerEndpointBoundedIteration
