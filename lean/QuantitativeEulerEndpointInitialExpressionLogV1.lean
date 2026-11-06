module

public import QuantitativeEulerEndpointActualInitialExpressionsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrimeBlocks

theorem log_max_polynomial_envelope (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) {M A x : ℝ} (hM : 1≤M) (hA : 1≤A)
    (r n : ℕ) (hx : x≤A*(envelope N hN excluded threshold M n n)^r) :
    Real.log (max 1 x)≤(Real.log A+2*(r:ℝ)*envelopeConstant N hN excluded threshold M)*(4:ℝ)^n := by
  have hV : 1≤envelope N hN excluded threshold M n n :=
    hM.trans (envelope_base N hN excluded threshold (by linarith) n n)
  have hpow : 1≤(envelope N hN excluded threshold M n n)^r := one_le_pow₀ hV
  have hfront : 1≤A*(envelope N hN excluded threshold M n n)^r := by nlinarith
  exact log_polynomial_envelope N hN excluded threshold hM hA
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) r n (max_le hfront hx)

#print axioms log_max_polynomial_envelope
end QuantitativeEulerEndpointPrimeBlocks

namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ)
    (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs ε : ℝ) (t : ℕ)


theorem exists_actual_initial_row_log (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) (hε : 0<ε) :
    ∃ Q : ℝ, 0≤Q ∧ ∀ n : ℕ,
      Real.log (max 1 (actualInitialRowCosts N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n).1)≤Q*(4:ℝ)^n ∧
      Real.log (max 1 (actualInitialRowCosts N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n).2)≤Q*(4:ℝ)^n := by
  obtain ⟨M,hM,hbound⟩ := exists_actual_initial_row_costs N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t
    hBg0 hD0 hH₀ hG0 hC0 hK0 hε
  have hM1 : 1≤M := by linarith
  let K := envelopeConstant N hN excluded threshold₀ M
  have hK : 0≤K := envelopeConstant_nonneg N hN excluded threshold₀ hM1
  let A : ℝ := 6*(36*9^t)^2
  have hA : 1≤A := by
    have hp : (1:ℝ)≤9^t := one_le_pow₀ (by norm_num)
    dsimp only [A]
    nlinarith
  let Q₁ := Real.log A+2*((936+5184*t:ℕ):ℝ)*K
  let Q₂ := Real.log 36+2*(432:ℝ)*K
  have hQ₁ : 0≤Q₁ := by dsimp only [Q₁]; exact add_nonneg (Real.log_nonneg hA) (by positivity)
  have hQ₂ : 0≤Q₂ := by dsimp only [Q₂]; exact add_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  refine ⟨Q₁+Q₂,add_nonneg hQ₁ hQ₂,?_⟩
  intro n
  have hm := log_max_polynomial_envelope N hN excluded threshold₀ hM1 hA (936+5184*t) n (hbound n).1
  have hh := log_max_polynomial_envelope N hN excluded threshold₀ hM1 (by norm_num : (1:ℝ)≤36) 432 n (hbound n).2
  exact ⟨hm.trans (mul_le_mul_of_nonneg_right (show Q₁≤Q₁+Q₂ by linarith) (by positivity)),
    hh.trans (mul_le_mul_of_nonneg_right (show Q₂≤Q₁+Q₂ by linarith) (by positivity))⟩

#print axioms exists_actual_initial_row_log
end QuantitativeEulerEndpointPrepared
