module

public import QuantitativeEulerEndpointActualReplacementRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointNestedPerturbation
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

def actualFiniteExpression (n : ℕ) (s : ℝ) (q : ℕ → ℝ[X]) : Expression :=
  let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
  let E := QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N) s e
  QuantitativeEulerEndpointTerminalExpression.iterate A P
    (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E)
    (fun j => power (effortAt A P e n b j)) q n

theorem actualFiniteExpression_error (n : ℕ) (s : ℝ) (F : ℕ → Algebra A P) (q : ℕ → ℝ[X])
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1)
    (hrec : ∀ j<n,F (j+1)=nextAt A P e n
      (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j (F j) (q j))
    (hq : ∀ j<n,ScalarSharpening (q j)) (x : UpperHalfPlane) :
    ‖rep A P (F n) x-regularSum
      (actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n s q) x‖≤
      comparisonBudget (fun j => power (effortAt A P e n
        (actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n*Real.exp (-8*s) := by
  apply common_expression_comparison A P e n _ s F q _ hinit hF hrec hq
  · intro j _ i x
    exact actualBlock_uncomposed_norm A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j i x
  · intro j _ x
    exact actualGramExpressions_regular A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n _ j x

/-- The literal finite expression for the actual bounded blocks has error
at most 2/4^n. The accuracy constant is fixed before the horizon and before
the sharpening polynomials or regular root are selected. -/
theorem exists_actual_finite_approximation (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
      ∀ F : ℕ → Algebra A P,∀ q : ℕ → ℝ[X],
      F 0=1 → (∀ j<n,0≤F j ∧ F j≤1) →
      (∀ j<n,F (j+1)=nextAt A P e n b j (F j) (q j)) →
      (∀ j<n,ScalarSharpening (q j)) →
      (∀ j<n,(q j).natDegree≤16*(sharpnessAt A P e n b (j+1))^5+1) →
      (∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤
        (((16*(sharpnessAt A P e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P e n b (j+1))^5)) →
      ∀ x,‖rep A P (F n) x-regularSum (actualFiniteExpression A P e hN excluded threshold
        S hS W B Bg D H₀ G C Kobs n (Real.exp ((K+1)*(4:ℝ)^n)) q) x‖≤2/(4:ℝ)^n := by
  obtain ⟨K,hK,hbudget⟩ := exists_actual_comparison_bound A P hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨K,hK,?_⟩
  intro n b F q hi hF hr hq hd hm x
  have he := actualFiniteExpression_error A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n (Real.exp ((K+1)*(4:ℝ)^n)) F q hi hF hr hq x
  have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hK
    (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) (hbudget n q hd hm)
  apply he.trans
  rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
  nlinarith only [hp]

#print axioms actualFiniteExpression_error
#print axioms exists_actual_finite_approximation
end QuantitativeEulerEndpointBoundedIteration
