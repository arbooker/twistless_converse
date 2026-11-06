module

public import QuantitativeHolomorphicGrowingFoldV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def lowerInverseGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  16*countReconstructionBound A P/(AsymptoticReconstructedCount.parameters A P).ε+
    newtonAmplificationConstant A P C+C+8

theorem growing_lower_inverse (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    (lowerCutoff A P D (Real.exp (-8*s)) n)⁻¹≤
      Real.exp (lowerInverseGrowthConstant A P C*s^4) := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let V := amplification n
  let K := newtonAmplificationConstant A P C
  let B := countReconstructionBound A P
  let ε := (AsymptoticReconstructedCount.parameters A P).ε
  let Q := 16*B/ε
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (countReconstructionBound_one_le A P)
  have hε : 0<ε := (AsymptoticReconstructedCount.parameters A P).epsilon_pos
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hV : 0<V := amplification_pos n
  have hVE : V≤Real.exp (K*s^4) := (growing_newton_complexity A P hC hs d hd).2.2
  have hDE : D≤4*Real.exp (C*s^2) := by
    have he : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
    dsimp [D]
    linarith
  have heq : (lowerCutoff A P D (Real.exp (-8*s)) n)⁻¹=
      (4*B/ε)*V*D*Real.exp (8*s) := by
    change (ε/B*(Real.exp (-8*s)/4)/(V*D))⁻¹=_
    rw [show Real.exp (-8*s)=(Real.exp (8*s))⁻¹ by rw [←Real.exp_neg]; congr 1; ring]
    field_simp
  change (lowerCutoff A P D (Real.exp (-8*s)) n)⁻¹≤_
  rw [heq]
  have hm := mul_le_mul hVE hDE hD.le (Real.exp_nonneg _)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤4*B/ε)
  have hm'' := mul_le_mul_of_nonneg_right hm' (Real.exp_nonneg (8*s))
  have hprod : (4*B/ε)*V*D*Real.exp (8*s)≤
      Q*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s) := by
    dsimp only [Q]
    convert hm'' using 1 <;> ring
  apply hprod.trans
  have hQE : Q≤Real.exp Q := by linarith [Real.add_one_le_exp Q]
  have hh := mul_le_mul_of_nonneg_right hQE
    (by positivity : 0≤Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s))
  have hh' : Q*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s)≤
      Real.exp (Q+K*s^4+C*s^2+8*s) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_add]
    convert hh using 1 <;> ring
  apply hh'.trans
  apply Real.exp_le_exp.mpr
  have hs2 : 1≤s^2 := by nlinarith
  have hs24 : s^2≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
  have hs4 : 1≤s^4 := hs2.trans hs24
  have hss4 : s≤s^4 := (by nlinarith : s≤s^2).trans hs24
  change Q+K*s^4+C*s^2+8*s≤(Q+K+C+8)*s^4
  nlinarith [mul_le_mul_of_nonneg_left hs4 hQ.le,mul_le_mul_of_nonneg_left hs24 hC]

theorem errorBudget_eq_inverse_eighth (s : ℝ) :
    Real.exp (-8*s)=((Real.exp s)^8)⁻¹ := by
  rw [←Real.exp_nat_mul,←Real.exp_neg]
  congr 1
  norm_num

#print axioms growing_lower_inverse

end QuantitativeHolomorphic.Schedule
