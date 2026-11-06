module

public import QuantitativeEulerEndpointActualGramCostsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem exists_actual_gram_exponential (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) :
    ∃ K : ℝ,0≤K ∧ ∀ n j : ℕ,j≤n → ∀ u : Expression,∀ R : ℝ,0≤R →
      expressionBound u≤R → ExpressionMatrixBound u R →
      let g := actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j
      expressionBound g≤Real.exp (K*(4:ℝ)^n)*R^2 ∧
      ExpressionMatrixBound g (Real.exp (K*(4:ℝ)^n)*R^2) := by
  obtain ⟨M,hM,hcost⟩ := exists_actual_gram_costs A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    hBg0 hD0 hH₀ hG0 hC0
  have hM1 : 1≤M := by linarith
  let t := (AsymptoticReconstructedCount.parameters A P).s+4
  let a : ℝ := 2*(72*9^t)^2
  let K₁ := Real.log a+2*((684+720*t:ℕ):ℝ)*envelopeConstant N hN excluded threshold M
  let K₂ := Real.log (8*36^2)+2*(720:ℝ)*envelopeConstant N hN excluded threshold M
  have ha : 1≤a := by
    have hp : (1:ℝ)≤9^t := one_le_pow₀ (by norm_num)
    dsimp only [a]
    nlinarith
  have hc := envelopeConstant_nonneg N hN excluded threshold hM1
  have hk₁ : 0≤K₁ := add_nonneg (Real.log_nonneg ha) (by positivity)
  have hk₂ : 0≤K₂ := add_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  refine ⟨K₁+K₂,add_nonneg hk₁ hk₂,?_⟩
  intro n j hj u R hR hu huM g
  have hs (c : ℝ) (hca : 1≤c) (r : ℕ) :
      c*(envelope N hN excluded threshold M n n)^r≤
        Real.exp ((Real.log c+2*(r:ℝ)*envelopeConstant N hN excluded threshold M)*(4:ℝ)^n) := by
    have hl := log_max_polynomial_envelope N hN excluded threshold hM1 hca r n
      (le_refl (c*(envelope N hN excluded threshold M n n)^r))
    have he := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))] at he
    exact (le_max_right _ _).trans he
  have h₁ := (hs a ha (684+720*t)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show K₁≤K₁+K₂ by linarith) (by positivity)))
  have h₂ := (hs (8*36^2) (by norm_num) 720).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show K₂≤K₁+K₂ by linarith) (by positivity)))
  have hh := hcost n j hj u R hR hu huM
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right h₁ (sq_nonneg R)),
    hh.2.mono (mul_le_mul_of_nonneg_right h₂ (sq_nonneg R))⟩

theorem exp_times_double_exp_square {a c R : ℝ} (ha : 0≤a) (hc : 0≤c) (hR : 1≤R) :
    Real.exp (a*R)*(Real.exp (Real.exp (c*R)))^2≤Real.exp (Real.exp ((a+c+3)*R)) := by
  rw [pow_two,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hR0 : 0≤R := by linarith
  have h₁ : a*R≤Real.exp ((a+c)*R) := by
    have he := Real.add_one_le_exp (a*R)
    have hm := Real.exp_le_exp.mpr (show a*R≤(a+c)*R by nlinarith)
    linarith
  have h₂ : Real.exp (c*R)≤Real.exp ((a+c)*R) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hs := QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le
    (a:=a+c) (by norm_num : (0:ℝ)≤3) hR
  have he : (3+(a+c))*R=(a+c+3)*R := by ring
  rw [he] at hs
  linarith

#print axioms exists_actual_gram_exponential
#print axioms exp_times_double_exp_square
end QuantitativeEulerEndpointBoundedIteration
