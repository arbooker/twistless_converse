module

public import QuantitativeHolomorphicGrowingFilterScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

theorem quartic_exp_decay {s : ℝ} (hs : 0≤s) :
    s^4*Real.exp (-4*s)≤24*Real.exp (-3*s) := by
  have h := Real.pow_div_factorial_le_exp s hs 4
  norm_num at h
  have hp : s^4≤24*Real.exp s := by linarith
  calc
    _ ≤24*Real.exp s*Real.exp (-4*s) := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc,←Real.exp_add]; congr 2; ring

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def approximationGrowthConstant (P : Parameters A) (C M : ℝ) : ℝ :=
  24*(2+2*((Real.sqrt (countGramLower A P))⁻¹^2+
    4*(newtonGrowthConstant A P C+2)^2)*M)

theorem growing_sharp_majorant (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
    Sharp.countFilterMajorant A P n≤
      ((Real.sqrt (countGramLower A P))⁻¹^2+4*(newtonGrowthConstant A P C+2)^2)*s^4 := by
  dsimp only
  let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
  have hn := (growing_newton_complexity A P hC hs d hd).2.1
  have hp : ((3/2:ℝ)^n)^2≤(4:ℝ)^n := by
    rw [←pow_mul,pow_mul']
    exact pow_le_pow_left₀ (by positivity) (by norm_num) n
  have hs4 : 1≤s^4 := by simpa using pow_le_pow_right₀ hs (by norm_num : 0≤4)
  unfold Sharp.countFilterMajorant
  apply max_le
  · have hm := mul_le_mul_of_nonneg_left hs4 (sq_nonneg ((Real.sqrt (countGramLower A P))⁻¹))
    nlinarith [mul_nonneg (sq_nonneg (newtonGrowthConstant A P C+2)) (by positivity : 0≤s^4)]
  · apply (hp.trans hn).trans
    nlinarith [mul_nonneg (sq_nonneg ((Real.sqrt (countGramLower A P))⁻¹)) (by positivity : 0≤s^4)]

/-- The literal reconstruction-filter error at the simultaneous cutoffs,
including the sharp Newton majorant, has an explicit X^-3 bound. -/
theorem growing_reconstruction_approximation (P : Parameters A) {C s M : ℝ}
    (hC : 0≤C) (hs : 1≤s) (hM : 0≤M) (d : ℕ)
    (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    let J := foldCutoff A P D (Real.exp (-8*s)) j n
    let Y := lowerCutoff A P D (Real.exp (-8*s)) n
    (2+2*Sharp.countFilterMajorant A P n*M)*Real.sqrt (countFilterError A P Y j J n d)≤
      approximationGrowthConstant A P C M*Real.exp (-3*s) := by
  dsimp only
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let j := reconstructionDepth A P D (Real.exp (-8*s)) n
  let J := foldCutoff A P D (Real.exp (-8*s)) j n
  let Y := lowerCutoff A P D (Real.exp (-8*s)) n
  let c := (Real.sqrt (countGramLower A P))⁻¹^2+4*(newtonGrowthConstant A P C+2)^2
  have hc : 0≤c := by dsimp [c]; positivity
  have herr := countFilterError_schedule A P d (Real.exp_pos (-8*s))
  have hsqrt : Real.sqrt (countFilterError A P Y j J n d)≤Real.exp (-4*s) := by
    apply (Real.sqrt_le_sqrt herr.2.2.2).trans_eq
    rw [show Real.exp (-8*s)=(Real.exp (-4*s))^2 by
      rw [←Real.exp_nat_mul]; congr 1; ring]
    exact Real.sqrt_sq (Real.exp_nonneg _)
  have hmajor := growing_sharp_majorant A P hC hs d hd
  have hs4 : 1≤s^4 := by simpa using pow_le_pow_right₀ hs (by norm_num : 0≤4)
  have hfront : 2+2*Sharp.countFilterMajorant A P n*M≤(2+2*c*M)*s^4 := by
    have hm := mul_le_mul_of_nonneg_right hmajor hM
    nlinarith only [hm,hs4]
  have hq := quartic_exp_decay (by linarith : 0≤s)
  calc
    _ ≤ ((2+2*c*M)*s^4)*Real.exp (-4*s) :=
      mul_le_mul hfront hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = (2+2*c*M)*(s^4*Real.exp (-4*s)) := by ring
    _ ≤ (2+2*c*M)*(24*Real.exp (-3*s)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by unfold approximationGrowthConstant; dsimp [c]; ring

#print axioms growing_reconstruction_approximation

end QuantitativeHolomorphic.Schedule
