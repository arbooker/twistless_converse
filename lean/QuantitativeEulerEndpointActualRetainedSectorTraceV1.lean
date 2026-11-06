module

public import QuantitativeEulerEndpointCommonRetainedTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticDiagonalTrace
open QuantitativeHolomorphic QuantitativeEulerEndpointCommonReconstruction
open QuantitativeEulerEndpointSector
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem terminalCompression_norm_le
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :
    ‖terminalCompression A P F‖≤‖F‖ := by
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  have hi : ∀ v,‖S v‖=‖v‖ := (norm_map_iff_adjoint_comp_self S).mpr
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hn : ‖S‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [hi,one_mul]
  have ha : ‖S.adjoint‖≤1 := by rwa [adjoint.norm_map]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
  rw [one_mul]
  exact (opNorm_comp_le _ _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg F))

theorem ambient_sector_finrank_le_retained (hN : 0<N) {s : ℝ} (hs : 1≤s) (h : ℕ) (e : Sector N)
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hF : 0≤F) (hFn : ‖F‖≤1) (δ : ℝ)
    (herr : ‖F*normalizedPhysicalSectorProjection A P hN h e-normalizedPhysicalSectorProjection A P hN h e‖≤δ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      upperCutTrace (physicalCylinder A P hN s e h) (terminalCompression A P F) (2*h) (P'.s+4)
        (by positivity : 0<4*Real.pi) P'.epsilon_pos (Real.exp (16*s))+
          (2*h+2:ℝ)*retainedTraceError A P s h := by
  have hd := ambient_sector_finrank_mul_le_trace A P hN h e F hF δ herr
  have ht := physicalCylinder_retained_trace_rate A P hN hs e h (terminalCompression A P F)
    ((terminalCompression_norm_le A P F).trans hFn)
  have he := (div_le_iff₀ (by positivity : (0:ℝ)<2*h+2)).mp ht
  have hl := le_abs_self (trace (fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
      (by positivity : 0<4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos)
      (compressedSandwich (normalizedCountReconstruction A hN P h e) (terminalCompression A P F)
        (holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
          (by positivity : 0<4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos))-
    upperCutTrace (physicalCylinder A P hN s e h) (terminalCompression A P F) (2*h)
      ((AsymptoticReconstructedCount.parameters A P).s+4) (by positivity : 0<4*Real.pi)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos (Real.exp (16*s)))
  rw [Real.norm_eq_abs] at he
  dsimp only at hd ⊢
  nlinarith only [hd,he,hl]

#print axioms terminalCompression_norm_le
#print axioms ambient_sector_finrank_le_retained
end QuantitativeEulerEndpointApproximateTrace

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointApproximateTrace
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticDiagonalTrace
open QuantitativeEulerEndpointCommonReconstruction
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_sector_retained_trace (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let F := holomorphicSum (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      upperCutTrace (physicalCylinder A P (NeZero.pos N) (Real.exp ((K+1)*(4:ℝ)^n)) e h)
        (terminalCompression A P F) (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
        (Real.exp (16*Real.exp ((K+1)*(4:ℝ)^n)))+
      (2*h+2:ℝ)*retainedTraceError A P (Real.exp ((K+1)*(4:ℝ)^n)) h := by
  have hs : 1≤Real.exp ((K+1)*(4:ℝ)^n) := Real.one_le_exp (by positivity)
  have ho := actualFiniteExpression_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq
  apply ambient_sector_finrank_le_retained A P (NeZero.pos N) hs h e _ ho.1
  · exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ ho.1).mpr ho.2.1
  · exact actualFiniteExpression_sector_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h hK q hq hbudget

#print axioms actualFiniteExpression_sector_retained_trace
end QuantitativeEulerEndpointBoundedIteration
