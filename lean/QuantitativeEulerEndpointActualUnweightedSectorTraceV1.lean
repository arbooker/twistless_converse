module

public import QuantitativeEulerEndpointCommonTraceExpressionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFiniteBranch AsymptoticUnweightedKernel
open QuantitativeHolomorphic QuantitativeEulerEndpointCommonReconstruction QuantitativeEulerEndpointSector
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The original sector rank is bounded by the unweighted physical trace
of a literal finite branch expression. All reconstruction, truncation and
weighted-mode errors are explicit. -/
theorem sector_finrank_le_unweighted_expression (hN : 0<N) {s : ℝ} (hs : 1≤s) (h : ℕ) (e : Sector N)
    (T : Expression) (hT : 0≤holomorphicSum T (h+1)) (hTn : ‖holomorphicSum T (h+1)‖≤1) (δ : ℝ)
    (herr : ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hN h e-
      normalizedPhysicalSectorProjection A P hN h e‖≤δ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      liftedTrace h P'.epsilon_pos (holomorphicSum
        (retainedExpression (lowerHeight A P s) (Real.exp (16*s)) (sandwichExpression A P hN s e T)) (h+1))+
      (2*h+2:ℝ)*(retainedTraceError A P s h+weightedTraceError A P s h) := by
  intro P'
  have hd := ambient_sector_finrank_le_retained A P hN hs h e (holomorphicSum T (h+1)) hT hTn δ herr
  have hw := physicalCylinder_weighted_trace_error A P hN hs e h
    (terminalCompression A P (holomorphicSum T (h+1)))
    ((terminalCompression_norm_le A P _).trans hTn) (Real.exp (16*s))
  have he := (div_le_iff₀ (by positivity : (0:ℝ)<2*h+2)).mp hw
  rw [sandwichExpression_lifted_trace]
  have hl := le_abs_self (upperCutTrace (physicalCylinder A P hN s e h)
      (terminalCompression A P (holomorphicSum T (h+1))) (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos (Real.exp (16*s))-
    upperCutTrace (physicalCylinder A P hN s e h) (terminalCompression A P (holomorphicSum T (h+1)))
      (2*h) 0 (by positivity : 0<4*Real.pi) P'.epsilon_pos (Real.exp (16*s)))
  rw [Real.norm_eq_abs] at he
  dsimp only at hd ⊢
  nlinarith only [hd,he,hl]

#print axioms sector_finrank_le_unweighted_expression
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

theorem actualFiniteExpression_sector_unweighted_trace (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let T := actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q
    let s := Real.exp ((K+1)*(4:ℝ)^n)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)≤
      AsymptoticUnweightedKernel.liftedTrace h P'.epsilon_pos (holomorphicSum
        (retainedExpression (lowerHeight A P s) (Real.exp (16*s)) (sandwichExpression A P (NeZero.pos N) s e T)) (h+1))+
      (2*h+2:ℝ)*(retainedTraceError A P s h+weightedTraceError A P s h) := by
  have hs : 1≤Real.exp ((K+1)*(4:ℝ)^n) := Real.one_le_exp (by positivity)
  have ho := actualFiniteExpression_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq
  apply sector_finrank_le_unweighted_expression A P (NeZero.pos N) hs h e _ ho.1
  · exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ ho.1).mpr ho.2.1
  · exact actualFiniteExpression_sector_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h hK q hq hbudget

#print axioms actualFiniteExpression_sector_unweighted_trace
end QuantitativeEulerEndpointBoundedIteration
