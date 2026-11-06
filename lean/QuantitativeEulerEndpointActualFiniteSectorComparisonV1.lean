module

public import QuantitativeEulerEndpointFiniteSectorComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointApproximateTrace
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticDiagonalTrace
open QuantitativeEulerEndpointCommonReconstruction
open QuantitativeHolomorphic.Schedule AsymptoticRegularTrace MeasureTheory
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_sector_regular_comparison (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    {M : ℝ} (hM : 0≤M)
    (hm : ExpressionMatrixBound (sandwichExpression A P (NeZero.pos N)
      (Real.exp ((K+1)*(4:ℝ)^n)) e
      (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
        n (Real.exp ((K+1)*(4:ℝ)^n)) q)) M)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(M*(Real.exp (16*Real.exp ((K+1)*(4:ℝ)^n))+2))≤1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let T := actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q
    let s := Real.exp ((K+1)*(4:ℝ)^n)
    let E := sandwichExpression A P (NeZero.pos N) s e T
    let Y := lowerHeight A P s
    let H := Real.exp (16*s)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ)≤
      signedTrace volume (regularSum (retainedExpression Y H E))/(4*Real.pi)+
      retainedTraceError A P s h+weightedTraceError A P s h+
      expressionBound E*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card := by
  have hs : 1≤Real.exp ((K+1)*(4:ℝ)^n) := Real.one_le_exp (by positivity)
  have ho := actualFiniteExpression_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq
  apply sector_finrank_le_retained_regular A P (NeZero.pos N) hs h e _ ho.1 _ _ _ hM hm hsmall
  · exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ ho.1).mpr ho.2.1
  · exact actualFiniteExpression_sector_paid A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h hK q hq hbudget

#print axioms actualFiniteExpression_sector_regular_comparison
end QuantitativeEulerEndpointBoundedIteration
