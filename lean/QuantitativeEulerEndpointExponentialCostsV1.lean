module

public import QuantitativeEulerEndpointExponentialParametersV1
public import QuantitativeEulerEndpointNestedCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointExponentialParameters
open Polynomial

theorem power_exp_upper {E : ℝ} (hE : 0≤E) :
    (power E:ℝ)+1≤34*Real.exp (2*E) := by
  have he : E≤Real.exp E := by linarith [Real.add_one_le_exp E]
  have he1 : 1≤Real.exp E := Real.one_le_exp_iff.mpr hE
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_pos E).le
  have hup := power_upper hE
  have hid : Real.exp (2*E)=(Real.exp E)^2 := by simpa only [Nat.cast_ofNat] using Real.exp_nat_mul E 2
  rw [hid]
  nlinarith

theorem power_log_upper {E : ℝ} (hE : 0≤E) :
    Real.log ((power E:ℝ)+1)≤Real.log 34+2*E := by
  have h := Real.log_le_log (by positivity : 0<(power E:ℝ)+1) (power_exp_upper hE)
  simpa only [Real.log_mul (by norm_num : (34:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] using h

theorem sharpness_exp_upper {D E : ℝ} (hD : 0≤D) (hE : 0≤E) :
    (sharpness D E:ℝ)+1≤(280*D+3)*Real.exp (3*E) := by
  let e := Real.exp E
  have he : E≤e := by dsimp only [e]; linarith [Real.add_one_le_exp E]
  have he1 : 1≤e := Real.one_le_exp_iff.mpr hE
  have he0 : 0≤e := by linarith
  have hpower : (power E:ℝ)≤33*e^2 := by
    have hp := power_upper hE
    have hm := mul_le_mul_of_nonneg_right he he0
    dsimp only [e] at hm ⊢
    nlinarith
  have hJ : (sharpness D E:ℝ)≤4*D*(4+2*(power E:ℝ))*E+2 := by
    have hh := (Nat.ceil_lt_add_one (show 0≤4*D*(4+2*(power E:ℝ))*E by positivity)).le
    unfold sharpness
    push_cast
    linarith
  have hrow : 4+2*(power E:ℝ)≤70*e^2 := by nlinarith
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hrow (show 0≤4*D by positivity)) he hE
      (show 0≤4*D*(70*e^2) by positivity)
  have he3 : 1≤e^3 := one_le_pow₀ he1
  have hid : Real.exp (3*E)=e^3 := by simpa only [Nat.cast_ofNat] using Real.exp_nat_mul E 3
  rw [hid]
  nlinarith only [hJ,hm,he3]

theorem sharpness_log_upper {D E : ℝ} (hD : 0≤D) (hE : 0≤E) :
    Real.log ((sharpness D E:ℝ)+1)≤Real.log (280*D+3)+3*E := by
  have h := Real.log_le_log (by positivity : 0<(sharpness D E:ℝ)+1) (sharpness_exp_upper hD hE)
  simpa only [Real.log_mul (by positivity : 280*D+3≠0) (Real.exp_ne_zero _),Real.log_exp] using h

theorem sharpening_degree_log {q : ℝ[X]} {J : ℕ} (hq : q.natDegree≤16*J^5+1) :
    Real.log (q.natDegree+1:ℝ)≤Real.log 18+5*Real.log (J+1:ℝ) := by
  have hq' : (q.natDegree:ℝ)+1≤16*(J:ℝ)^5+2 := by exact_mod_cast (show q.natDegree+1≤16*J^5+2 by omega)
  have hpow : (J:ℝ)^5≤((J:ℝ)+1)^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hpow1 : (1:ℝ)≤((J:ℝ)+1)^5 := one_le_pow₀ (by have h := Nat.cast_nonneg (α:=ℝ) J; linarith)
  have hh : (q.natDegree:ℝ)+1≤18*((J:ℝ)+1)^5 := by linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<q.natDegree+1) hh
  simpa only [Real.log_mul (by norm_num : (18:ℝ)≠0) (by positivity : ((J:ℝ)+1)^5≠0),
    Real.log_pow,Nat.cast_ofNat] using hl

/-- The exact scheduled depth and next-block sharpening pay only linear
logarithmic complexity in the two adjacent efforts. -/
theorem scheduled_logarithmic_cost {D E F : ℝ} (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (q : ℝ[X]) (hq : q.natDegree≤16*(sharpness D F)^5+1) :
    Real.log 8+Real.log (q.natDegree+1:ℝ)+Real.log ((power E:ℝ)+1)≤
      (Real.log 8+Real.log 18+5*Real.log (280*D+3)+Real.log 34)+15*F+2*E := by
  have hd := sharpening_degree_log hq
  have hs := sharpness_log_upper hD hF
  have hp := power_log_upper hE
  linarith

#print axioms power_log_upper
#print axioms sharpness_log_upper
#print axioms scheduled_logarithmic_cost
end QuantitativeEulerEndpointExponentialParameters
