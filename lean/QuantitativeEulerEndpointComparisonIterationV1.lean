module

public import QuantitativeEulerEndpointComparisonBudgetV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedPerturbation
open Polynomial QuantitativeEulerEndpointResidual
open QuantitativeEulerEndpointSoftUpdate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Operator-norm comparison for the entire actual nested update, paying
perturbations of every Gram. All order assumptions refer to the two actual
sequences being compared. -/
theorem iteration_difference (F V G T : ℕ → H →L[ℂ] H)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) {δ : ℝ} (hδ : 0≤δ)
    (hinit : ‖F 0-V 0‖≤δ)
    (hF : ∀ j,j<n → 0≤F j ∧ F j≤1) (hV : ∀ j,j<n → 0≤V j ∧ V j≤1)
    (hG : ∀ j,j<n → 0≤G j ∧ G j≤1) (hT : ∀ j,j<n → 0≤T j ∧ T j≤1)
    (hrecF : ∀ j,j<n → F (j+1)=aeval (update (F j) (F j*G j*F j) (L j)) (q j))
    (hrecV : ∀ j,j<n → V (j+1)=aeval (update (V j) (V j*T j*V j) (L j)) (q j))
    (hgram : ∀ j,j<n → ‖G j-T j‖≤δ) :
    ‖F n-V n‖≤comparisonBudget L q n*δ := by
  induction n with
  | zero => simpa only [comparisonBudget,one_mul] using hinit
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    have hprev := ih (fun j hj => hF j (by omega)) (fun j hj => hV j (by omega))
      (fun j hj => hG j (by omega)) (fun j hj => hT j (by omega))
      (fun j hj => hrecF j (by omega)) (fun j hj => hrecV j (by omega))
      (fun j hj => hgram j (by omega))
    rw [hrecF n hn,hrecV n hn]
    exact (sharpened_difference (F n) (V n) (G n) (T n)
      (hF n hn) (hV n hn) (hG n hn) (hT n hn) (L n) (q n)).trans
      (comparisonBudget_step L q n hδ hprev (hgram n hn))

#print axioms iteration_difference
end QuantitativeEulerEndpointNestedPerturbation

namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeEulerEndpointResidual
open scoped Classical MatrixGroups

/-- Actual degree and mass estimates bound the operator-comparison budget,
in addition to the previously checked fixed-solution residual budget. -/
theorem exists_actual_comparison_bound {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let b := actualBlock A P hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n
      ∀ z : ℕ → ℝ[X],
      (∀ j,j<n → (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1) →
      (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤
        (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5)) →
      comparisonBudget (fun i => power (effortAt A P sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_residual_bound A P hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs hBg0 hD0 hH₀ hG0 hC0 hK0
  refine ⟨K+2,by positivity,?_⟩
  intro n b z hd hm
  have he := hbound n z hd hm
  exact (comparisonBudget_le_square _ z n).trans (squared_double_exp
    (one_le_pow₀ (by norm_num)) (by linarith [errorBudget_ge_one (fun i => power (effortAt A P sector n b i)) z n]) he)

#print axioms exists_actual_comparison_bound
end QuantitativeEulerEndpointBoundedIteration
