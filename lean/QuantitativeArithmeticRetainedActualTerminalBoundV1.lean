module

public import QuantitativeArithmeticRetainedHorizonScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointApproximateTrace
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticDiagonalTrace
open QuantitativeArithmeticRetainedNestedGeometricTrace QuantitativeArithmeticRetainedNestedCountComparison
open QuantitativeArithmeticRetainedApproximationSchedule QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedPacket
open QuantitativeHolomorphic.Schedule AsymptoticRegularTrace MeasureTheory
open QuantitativeArithmeticRetainedTerminalAlgebra
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)
    (hR₀ : ∀p∈R₀,p.Prime)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The actual common finite expression is a positive contraction in the
regular representation, with all concrete Gram hypotheses discharged. -/
theorem actualFiniteExpression_regular_order (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X])
    (hq : ∀j<n,ScalarSharpening (q j)) (x : UpperHalfPlane) :
    let T := actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q
    0≤regularSum T x ∧ regularSum T x≤1 := by
  let b := actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
  let E := QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ (NeZero.pos N) s e
  have hEn := QuantitativeArithmeticRetainedCommonExpression.regular_norm A P hR₀ (NeZero.pos N) s e x
  have hEp := QuantitativeArithmeticRetainedCommonExpression.regular_right_terminal A P hR₀ (NeZero.pos N) s e x
  have ht := QuantitativeArithmeticRetainedExpressionIteration.regular_order A P
    (actualGramExpressions A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun j => power (effortAt A P hR₀ e n b j)) q n x (by
      intro j hj
      rw [actualGramExpressions_regular]
      have ho := replacementGram_order A P e (b j).compact (b j).primes (b j).bound x
        (fun i => actualBlock_uncomposed_norm A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x)
        (regularSum E x) hEn
      have hs := replacementGram_support A P e (b j).compact (b j).primes (b j).bound x
        (regularSum E x) _ (QuantitativeArithmeticRetainedExpressionIteration.unit_regular_projection A P x) hEp
      exact ⟨ho.1,ho.2,hs⟩) hq
  exact ⟨ht.1,ht.2.1⟩

/-- The original sector dimension is bounded by the intrinsic prime-block
terminal trace and explicit reconstruction, weight, and finite-branch errors. -/
theorem actualFiniteExpression_sector_terminal_bound (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (n h : ℕ) {K : ℝ} (hK : 0≤K)
    (F : ℕ → Algebra A P) (q : ℕ → ℝ[X])
    (hinit : F 0=1) (hF : ∀ j≤n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n)))
    {M : ℝ} (hM : 0≤M)
    (hm : ExpressionMatrixBound (sandwichExpression A hR₀ (NeZero.pos N) P
      (tolerance (Real.exp ((K+1)*(4:ℝ)^n)) 0) e
      (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
        n (Real.exp ((K+1)*(4:ℝ)^n)) q)) M)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(M*(Real.exp (16*Real.exp ((K+1)*(4:ℝ)^n))+2))≤1) :
    let T := actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q
    let s := Real.exp ((K+1)*(4:ℝ)^n)
    let E := sandwichExpression A hR₀ (NeZero.pos N) P (tolerance s 0) e T
    let Y := lowerHeight A P (tolerance s 0)
    let H := Real.exp (16*s)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      (tr A P (F n)+(2/(4:ℝ)^n)*P.ε⁻¹)/(4*Real.pi)+
      QuantitativeArithmeticRetainedTraceComparison.traceError A P (tolerance s 0) H h+
      expressionBound E*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card := by
  let s := Real.exp ((K+1)*(4:ℝ)^n)
  let T := actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q
  have he (x) : ‖rep A P (F n) x-regularSum T x‖≤2/(4:ℝ)^n := by
    have herr := actualFiniteExpression_error A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n s F q hinit (fun j hj => hF j hj.le) hrec hq x
    have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hbudget
    apply herr.trans
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  have ht (x) : 0≤regularSum T x ∧ regularSum T x≤1 := by
    have hh := actualFiniteExpression_regular_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n s q hq x
    exact hh
  have hp := actualFiniteExpression_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs n h s q hq
  have hn : ‖holomorphicSum T (h+1)‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp.1).mpr hp.2.1
  have herr := actualFiniteExpression_sector_paid A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    hdiv hbad n h hK q hq hbudget
  have hs : 0≤s := (Real.exp_pos _).le
  exact sector_finrank_le_terminal A hR₀ (NeZero.pos N) P hdiv hbad (tolerance_pos s 0)
    (QuantitativeArithmeticRetainedScheduledTrace.accuracy_le_half hs) (Real.exp_pos (16*s)) h e T hp.1 hn
    (F n) (hF n le_rfl) ht (2/(4:ℝ)^n) (2/(4:ℝ)^n) herr he hM hm hsmall

#print axioms actualFiniteExpression_regular_order
#print axioms actualFiniteExpression_sector_terminal_bound
end QuantitativeArithmeticRetainedIteration
