module

public import QuantitativeHolomorphicGrowingNewtonV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

theorem binaryDepth_le_exponential {x B u : ℝ} (hx : 0≤x) (hB : 0≤B)
    (hu : 1≤u) (hxu : x≤Real.exp (B*u)) :
    (binaryDepth x:ℝ)≤((Real.log 6+B)/Real.log 2)*u := by
  have he : 1≤Real.exp (B*u) := Real.one_le_exp (by positivity)
  have harg : 2*(x+2)≤6*Real.exp (B*u) := by linarith
  have hl := Real.log_le_log (by positivity : 0<2*(x+2)) harg
  rw [Real.log_mul (by norm_num : (6:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] at hl
  have h6 : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  apply (binaryDepth_le_log hx).trans
  apply (div_le_iff₀ h2).mpr
  have heq : ((Real.log 6+B)/Real.log 2)*u*Real.log 2=(Real.log 6+B)*u := by field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hu h6]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def newtonAmplificationConstant (P : Parameters A) (C : ℝ) : ℝ :=
  4*(3+Real.log 7)*(newtonGrowthConstant A P C+2)^2

def reconstructionThresholdConstant (P : Parameters A) (C : ℝ) : ℝ :=
  32*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P)+
    newtonAmplificationConstant A P C+C+8

def reconstructionGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  (Real.log 6+reconstructionThresholdConstant A P C)/Real.log 2

theorem growing_reconstruction_threshold (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let x := (2*AsymptoticCertificateOperators.terminalConstant A
      (AsymptoticReconstructedCount.parameters A P)*amplification n*D)/(Real.exp (-8*s)/4)
    0≤x ∧ x≤Real.exp (reconstructionThresholdConstant A P C*s^4) := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let T := AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P)
  let K := newtonAmplificationConstant A P C
  let V := amplification n
  have hT : 0≤T := by dsimp [T,AsymptoticCertificateOperators.terminalConstant]; positivity
  have hV : 0≤V := (amplification_pos n).le
  have hD : 0≤D := by dsimp [D]; positivity
  have hK : 0≤K := by
    dsimp [K,newtonAmplificationConstant]
    have hl : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
    positivity
  have hE : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
  have hDE : D≤4*Real.exp (C*s^2) := by dsimp [D]; linarith
  have hVE : V≤Real.exp (K*s^4) := (growing_newton_complexity A P hC hs d hd).2.2
  have ht : Real.exp (-8*s)= (Real.exp (8*s))⁻¹ := by rw [←Real.exp_neg]; congr 1; ring
  have h32 : 32*T≤Real.exp (32*T) := by linarith [Real.add_one_le_exp (32*T)]
  have hrew : (2*T*V*D)/(Real.exp (-8*s)/4)=8*T*V*D*Real.exp (8*s) := by rw [ht]; field_simp; ring
  constructor
  · positivity
  · change (2*T*V*D)/(Real.exp (-8*s)/4)≤_
    rw [hrew]
    have hprod : 8*T*V*D*Real.exp (8*s)≤
        (32*T)*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s) := by
      have hm := mul_le_mul hVE hDE hD (Real.exp_nonneg _)
      have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤8*T)
      have hm'' := mul_le_mul_of_nonneg_right hm' (Real.exp_nonneg (8*s))
      convert hm'' using 1 <;> ring
    apply hprod.trans
    have hprod' := mul_le_mul_of_nonneg_right h32
      (by positivity : 0≤Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s))
    have hprod'' : (32*T)*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s)≤
        Real.exp (32*T+K*s^4+C*s^2+8*s) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_add]
      convert hprod' using 1 <;> ring
    apply hprod''.trans
    apply Real.exp_le_exp.mpr
    have hs2 : 1≤s^2 := by nlinarith
    have hs24 : s^2≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
    have hs14 : 1≤s^4 := hs2.trans hs24
    have hs4 : s≤s^4 := (by nlinarith : s≤s^2).trans hs24
    change 32*T+K*s^4+C*s^2+8*s≤(32*T+K+C+8)*s^4
    nlinarith [mul_le_mul_of_nonneg_left hs14 (by positivity : 0≤32*T),
      mul_le_mul_of_nonneg_left hs24 hC]

theorem growing_reconstruction_depth (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    (reconstructionDepth A P D (Real.exp (-8*s)) n:ℝ)≤reconstructionGrowthConstant A P C*s^4 := by
  have hx := growing_reconstruction_threshold A P hC hs d hd
  have hK : 0≤reconstructionThresholdConstant A P C := by
    unfold reconstructionThresholdConstant newtonAmplificationConstant
    have hl : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
    have hT : 0≤AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P) := by
      unfold AsymptoticCertificateOperators.terminalConstant
      positivity
    positivity
  have hs4 : 1≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
  exact binaryDepth_le_exponential hx.1 hK hs4 hx.2

#print axioms growing_reconstruction_threshold
#print axioms growing_reconstruction_depth

end QuantitativeHolomorphic.Schedule
