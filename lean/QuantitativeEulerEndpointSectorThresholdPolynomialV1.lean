module

public import QuantitativeEulerEndpointSectorCostPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSectorSigns QuantitativeSpectralObservability Polynomial
open scoped Classical MatrixGroups

/-- The rectangular distortion has a degree-ten polynomial majorant when
the matrix height is quartic and the source rectangle is linear. -/
def quarticDistortionPolynomial (l r₀ r₁ : ℝ) : Polynomial ℝ :=
  1+(C l*X^4*(C (2*r₁)*X+C (2*r₀+1)))^2

theorem quarticDistortionPolynomial_degree (l r₀ r₁ : ℝ) :
    (quarticDistortionPolynomial l r₀ r₁).natDegree≤10 := by
  unfold quarticDistortionPolynomial
  compute_degree!

theorem quarticDistortionPolynomial_bound (l r₀ r₁ x : ℝ) :
    wideDistortion (l*x^4) (r₁*x+r₀) (r₁*x+r₀)≤
      (quarticDistortionPolynomial l r₀ r₁).eval x := by
  simp only [quarticDistortionPolynomial,eval_add,eval_one,eval_pow,eval_mul,eval_C,eval_X]
  unfold wideDistortion
  have he : l*x^4*(r₁*x+r₀+(r₁*x+r₀)+1)=l*x^4*(2*r₁*x+(2*r₀+1)) := by ring
  rw [he]
  exact max_le (le_add_of_nonneg_right (sq_nonneg _)) (le_add_of_nonneg_left zero_le_one)

variable (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

def sectorThresholdPolynomial (W : Finset (List SL(2,ℤ))) (B ε K l r₀ r₁ : ℝ) (t : ℕ) : Polynomial ℝ :=
  C 2+C 4*sectorObservationPolynomial N hN sector S hS W B ε t*C K*
    (quarticDistortionPolynomial l r₀ r₁)^(2*t)

theorem sectorThresholdPolynomial_degree (W : Finset (List SL(2,ℤ)))
    (B ε K l r₀ r₁ : ℝ) (t : ℕ) :
    (sectorThresholdPolynomial N hN sector S hS W B ε K l r₀ r₁ t).natDegree≤32*t := by
  have hp := sectorObservationPolynomial_degree N hN sector S hS W B ε t
  have hd := natDegree_pow_le_of_le (2*t) (quarticDistortionPolynomial_degree l r₀ r₁)
  unfold sectorThresholdPolynomial
  rw [natDegree_C_add]
  apply (natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by simp : (C 4 : Polynomial ℝ).natDegree≤0) hp)
    (by simp : (C K : Polynomial ℝ).natDegree≤0)) hd).trans
  omega

/-- A polynomial majorizes the RECIPROCAL of the actual squared packet
cut. This is a cutoff-cost bound, not a small-spectrum mass bound. -/
theorem sectorThresholdPolynomial_bound (W : Finset (List SL(2,ℤ)))
    (B ε K l r₀ r₁ : ℝ) (hK : 0≤K) (t : ℕ) (x : ℝ) :
    let A := sectorObservationCost N hN sector S hS W B x ε t*
      (K*((wideDistortion (l*x^4) (r₁*x+r₀) (r₁*x+r₀))^t)^2)
    ((2*(1+2*A))⁻¹)⁻¹≤
      (sectorThresholdPolynomial N hN sector S hS W B ε K l r₀ r₁ t).eval x := by
  dsimp only
  rw [inv_inv]
  simp only [sectorThresholdPolynomial,eval_add,eval_C,eval_mul,eval_pow,
    sectorObservationPolynomial_eval]
  have hd := pow_le_pow_left₀ (wideDistortion_pos (l*x^4) (r₁*x+r₀) (r₁*x+r₀)).le
    (quarticDistortionPolynomial_bound l r₀ r₁ x) (2*t)
  have he : ((wideDistortion (l*x^4) (r₁*x+r₀) (r₁*x+r₀))^t)^2=
      (wideDistortion (l*x^4) (r₁*x+r₀) (r₁*x+r₀))^(2*t) := by rw [←pow_mul,Nat.mul_comm]
  rw [he]
  have ho := sectorObservationCost_nonneg N hN sector S hS W B x ε t
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) ho) hK)
  nlinarith only [hh]

#print axioms sectorThresholdPolynomial_degree
#print axioms sectorThresholdPolynomial_bound
end QuantitativeEulerEndpointPrepared
