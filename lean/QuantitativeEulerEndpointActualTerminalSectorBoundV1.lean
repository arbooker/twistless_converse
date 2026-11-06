module

public import QuantitativeEulerEndpointCommonRegularTraceV1

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
open QuantitativeEulerEndpointTerminalAlgebra
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The original sector dimension is bounded by the intrinsic prime-block
terminal trace and explicit reconstruction, weight, and finite-branch errors. -/
theorem actualFiniteExpression_sector_terminal_bound (n h : ℕ) {K : ℝ} (hK : 0≤K)
    (F : ℕ → Algebra A P) (q : ℕ → ℝ[X])
    (hinit : F 0=1) (hF : ∀ j≤n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j (F j) (q j))
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
      (tr A P (F n)+(2/(4:ℝ)^n)*P'.ε⁻¹)/(4*Real.pi)+
      retainedTraceError A P s h+weightedTraceError A P s h+
      expressionBound E*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card := by
  let s := Real.exp ((K+1)*(4:ℝ)^n)
  let T := actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q
  have he (x) : ‖rep A P (F n) x-regularSum T x‖≤2/(4:ℝ)^n := by
    have herr := actualFiniteExpression_error A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n s F q hinit (fun j hj => hF j hj.le) hrec hq x
    have hp := amplified_error_le hK (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hbudget
    apply herr.trans
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  have ht (x) : 0≤regularSum T x ∧ regularSum T x≤1 := by
    have hh := actualFiniteExpression_regular_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n s q hq x
    exact ⟨hh.1,hh.2.1⟩
  have hr := retained_regular_le_terminal A P (NeZero.pos N) s e (F n) (hF n le_rfl) T ht
    (2/(4:ℝ)^n) he (lowerHeight A P s) (Real.exp (16*s))
  have hc := actualFiniteExpression_sector_regular_comparison A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n h hK q hq hbudget hM hm hsmall
  have hd := div_le_div_of_nonneg_right hr (by positivity : 0≤4*Real.pi)
  dsimp only at hc ⊢
  linarith

#print axioms actualFiniteExpression_sector_terminal_bound
end QuantitativeEulerEndpointBoundedIteration
