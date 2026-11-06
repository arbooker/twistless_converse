module

public import QuantitativeHolomorphicScheduledTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def newtonGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  (|Real.log 4|+|Real.log 4|+|Real.log (Real.sqrt (countGramLower A P))|+C+8)/countGramLower A P

theorem newtonGrowthConstant_pos (P : Parameters A) {C : ℝ} (hC : 0≤C) :
    0<newtonGrowthConstant A P C := by
  unfold newtonGrowthConstant
  exact div_pos (by positivity) (countGramLower_pos A P)

/-- The actual Newton logarithmic threshold is quadratic in log X when the
literal filter degree is at most exp(C(log X)^2) and the target error is X^-8. -/
theorem growing_newton_threshold (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let c := countGramLower A P
    let x := Real.log (4*(2*d+2:ℝ)/(Real.exp (-8*s)*Real.sqrt c))/c
    0≤x ∧ x≤newtonGrowthConstant A P C*s^2 := by
  let c := countGramLower A P
  let D : ℝ := 2*d+2
  let E := Real.exp (C*s^2)
  have hc : 0<c := countGramLower_pos A P
  have hc1 : c≤1 := countGramLower_le_one A P
  have hsq : 0<Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq1 : Real.sqrt c≤1 := by simpa using Real.sqrt_le_sqrt hc1
  have hD : 0<D := by dsimp [D]; positivity
  have hD1 : 1≤D := by dsimp [D]; nlinarith [(Nat.cast_nonneg d : (0:ℝ)≤d)]
  have hE : 1≤E := Real.one_le_exp (by positivity)
  have hDE : D≤4*E := by dsimp [D,E] at *; linarith
  have ht : 0<Real.exp (-8*s) := Real.exp_pos _
  have ht1 : Real.exp (-8*s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hden : 0<Real.exp (-8*s)*Real.sqrt c := mul_pos ht hsq
  have hden1 : Real.exp (-8*s)*Real.sqrt c≤1 :=
    (mul_le_mul ht1 hsq1 hsq.le zero_le_one).trans_eq (one_mul _)
  have hR1 : 1≤4*D/(Real.exp (-8*s)*Real.sqrt c) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hlogD : Real.log D≤Real.log 4+C*s^2 := by
    have hl := Real.log_le_log hD hDE
    simpa only [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp,E] using hl
  have he : Real.log (4*D/(Real.exp (-8*s)*Real.sqrt c))=
      Real.log 4+Real.log D+8*s-Real.log (Real.sqrt c) := by
    rw [Real.log_div (mul_pos (by norm_num) hD).ne' hden.ne',
      Real.log_mul (by norm_num : (4:ℝ)≠0) hD.ne',
      Real.log_mul ht.ne' hsq.ne',Real.log_exp]
    ring
  have hs2 : 1≤s^2 := by nlinarith
  have hss : s≤s^2 := by nlinarith
  have hcst : Real.log 4+Real.log 4-Real.log (Real.sqrt c)≤
      |Real.log 4|+|Real.log 4|+|Real.log (Real.sqrt c)| := by
    linarith [le_abs_self (Real.log 4),neg_le_abs (Real.log (Real.sqrt c))]
  have hab0 : 0≤|Real.log 4|+|Real.log 4|+|Real.log (Real.sqrt c)| := by positivity
  have hab := mul_le_mul_of_nonneg_left hs2 hab0
  constructor
  · exact div_nonneg (Real.log_nonneg hR1) hc.le
  · change Real.log (4*D/(Real.exp (-8*s)*Real.sqrt c))/c≤_
    apply (div_le_iff₀ hc).mpr
    have hconst : newtonGrowthConstant A P C*c=
        |Real.log 4|+|Real.log 4|+|Real.log (Real.sqrt c)|+C+8 := by
      exact div_mul_cancel₀ _ hc.ne'
    have hrewrite : newtonGrowthConstant A P C*s^2*c=
        (|Real.log 4|+|Real.log 4|+|Real.log (Real.sqrt c)|+C+8)*s^2 := by
      rw [mul_right_comm,hconst]
    rw [hrewrite,he]
    nlinarith only [hlogD,hcst,hab,hss]

theorem growing_newton_complexity (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let K := newtonGrowthConstant A P C
    let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
    (2:ℝ)^n≤2*(K+2)*s^2 ∧
    (4:ℝ)^n≤4*(K+2)^2*s^4 ∧
    amplification n≤Real.exp (4*(3+Real.log 7)*(K+2)^2*s^4) := by
  let K := newtonGrowthConstant A P C
  let x := Real.log (4*(2*d+2:ℝ)/(Real.exp (-8*s)*Real.sqrt (countGramLower A P)))/countGramLower A P
  have hx := growing_newton_threshold A P hC hs d hd
  have hK : 0<K := newtonGrowthConstant_pos A P hC
  have hs2 : 1≤s^2 := by nlinarith
  have hxp : x+2≤(K+2)*s^2 := by dsimp only [x,K]; nlinarith only [hx.2,hs2]
  have hsq : (x+2)^2≤(K+2)^2*s^4 := by
    nlinarith [mul_self_le_mul_self (by linarith [hx.1] : 0≤x+2) hxp]
  refine ⟨(binaryDepth_power_upper x hx.1).trans (by nlinarith only [hxp]),
    (binaryDepth_complexity x hx.1).trans (by nlinarith only [hsq]),?_⟩
  apply (amplification_binaryDepth_le hx.1).trans
  apply Real.exp_le_exp.mpr
  have hl : 0≤3+Real.log 7 := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤7); linarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0≤4*(3+Real.log 7))]

#print axioms growing_newton_threshold
#print axioms growing_newton_complexity

end QuantitativeHolomorphic.Schedule
