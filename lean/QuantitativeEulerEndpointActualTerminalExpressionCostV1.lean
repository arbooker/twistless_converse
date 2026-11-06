module

public import QuantitativeEulerEndpointActualCommonGramCostV1
public import QuantitativeEulerEndpointActualExpressionApproxV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The ACTUAL full-terminal finite filter, with chosen original block
rows and common reconstruction, has uniform double-exponential coefficient
and integer-matrix complexity. No Gram-growth assumption is introduced. -/
theorem exists_actual_terminal_expression_cost (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) {K : ℝ} (hK : 0≤K) :
    ∃ C' : ℝ,0≤C' ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n
      ∀ q : ℕ → ℝ[X],
      (∀ j<n,(q j).natDegree≤16*(sharpnessAt A P e n b (j+1))^5+1) →
      (∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤
        (((16*(sharpnessAt A P e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P e n b (j+1))^5)) →
      let T := actualFiniteExpression A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
        n (Real.exp ((K+1)*(4:ℝ)^n)) q
      expressionBound T≤Real.exp (Real.exp (C'*(4:ℝ)^n)) ∧
      ExpressionMatrixBound T (Real.exp (Real.exp (C'*(4:ℝ)^n))) := by
  obtain ⟨Kg,hKg,hgram⟩ := exists_actual_common_gram_cost A P e hN excluded threshold S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK
  obtain ⟨Kq,hKq,hcoef⟩ := exists_actual_coefficient_bound A P hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  obtain ⟨Kl,hKl,hlog⟩ := exists_actual_logarithmic_cost A P hN excluded threshold e S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  let Cb := 16+Kg+Kq
  have hCb : 16≤Cb := by dsimp only [Cb]; linarith
  refine ⟨Kl+Cb,by linarith,?_⟩
  intro n b q hd hm T
  let E := QuantitativeEulerEndpointCommonReconstruction.expression A P (NeZero.pos N)
    (Real.exp ((K+1)*(4:ℝ)^n)) e
  let g := actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n E
  let R : ℝ := (4:ℝ)^n
  let B' := Real.exp (Real.exp (Cb*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hB' : 16≤B' := by
    have hcr : 16≤Cb*R := by nlinarith
    dsimp only [B']
    linarith [Real.add_one_le_exp (Cb*R),Real.add_one_le_exp (Real.exp (Cb*R))]
  have hg' (j : ℕ) (hj : j<n) : expressionBound (g j)≤B' ∧ ExpressionMatrixBound (g j) B' := by
    have hh := hgram n j hj.le
    have hb : Real.exp (Real.exp (Kg*R))≤B' :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp only [Cb]; nlinarith))
    exact ⟨hh.1.trans hb,hh.2.mono hb⟩
  have hq' (j : ℕ) (hj : j<n) : (∑ i∈(q j).support,|(q j).coeff i|)≤B' :=
    (hcoef n q hm j hj).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp only [Cb]; nlinarith)))
  have hb : Real.log B'≤Real.exp (Cb*R) := by
    dsimp only [B']
    rw [Real.log_exp]
  have ht := QuantitativeEulerEndpointTerminalExpression.bounds A P g
    (fun j => power (effortAt A P e n b j)) q hB' n (fun j hj => (hg' j hj).1)
    (fun j hj => (hg' j hj).2) hq' (hlog n q hd).1 hb
  have he : Kl*R+Cb*R=(Kl+Cb)*R := by ring
  rw [he] at ht
  exact ht

#print axioms exists_actual_terminal_expression_cost
end QuantitativeEulerEndpointBoundedIteration
