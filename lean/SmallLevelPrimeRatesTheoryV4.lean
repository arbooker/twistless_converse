module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelPrimeRates. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThreePrimeRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelPrimeRates
open Complex

def monomial (e : ℤ×ℤ×ℤ) (x y z : ℂ) : ℂ := x^e.1*y^e.2.1*z^e.2.2

theorem positive_zpow_cpow_direct {p : ℝ} (hp : 0<p) (e : ℤ) (s : ℂ) :
    ((p:ℂ)^e)^s=((p:ℂ)^s)^e := by
  have harg : (p:ℂ).arg=0 := arg_ofReal_of_nonneg hp.le
  rw [← Complex.cpow_int_mul' (by simp [harg,Real.pi_pos])
    (by simp [harg,Real.pi_pos.le]),Complex.cpow_int_mul]

theorem rational_power (p q r : ℕ) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (b : ℚ) (e : ℤ×ℤ×ℤ) (hb : b=(p:ℚ)^e.1*(q:ℚ)^e.2.1*(r:ℚ)^e.2.2)
    (s : ℂ) : (b:ℂ)^s=monomial e ((p:ℂ)^s) ((q:ℂ)^s) ((r:ℂ)^s) := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hreal : (b:ℝ)=(p:ℝ)^e.1*(q:ℝ)^e.2.1*(r:ℝ)^e.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_natCast] using
      congrArg (fun t : ℚ => (t:ℝ)) hb
  have hc : (b:ℂ)=(((p:ℝ)^e.1*(q:ℝ)^e.2.1*(r:ℝ)^e.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun t : ℝ => (t:ℂ)) hreal
  rw [hc,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow_direct hp',positive_zpow_cpow_direct hq',positive_zpow_cpow_direct hr']
  simp only [Complex.ofReal_natCast,monomial]

def parameter (p m : ℕ) (s : ℂ) : ℂ := (p:ℂ)^(s-(m:ℂ))

theorem parameter_ne_zero (p m : ℕ) (hp : p≠0) (s : ℂ) : parameter p m s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))

theorem parameter_analytic (p m : ℕ) (hp : p≠0) (s : ℂ) : AnalyticAt ℂ (parameter p m) s := by
  unfold parameter
  simp_rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp : (p:ℂ)≠0)]
  fun_prop

theorem parameter_shift (p m : ℕ) (hp : p≠0) (s : ℂ) :
    parameter p m (s-1)=parameter p m s/(p:ℂ) := by
  unfold parameter
  rw [show s-1-(m:ℂ)=(s-(m:ℂ))-1 by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one]

#print axioms rational_power
#print axioms parameter_analytic
end SmallLevelPrimeRates
end
end

/-! ## SmallLevelPrimeParameterNormV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelPrimeRates
open Complex

theorem parameter_add_nat (p m : ℕ) (hp : p≠0) (s : ℂ) (n : ℕ) :
    parameter p m (s+n)=parameter p m s*(p:ℂ)^n := by
  unfold parameter
  rw [show s+(n:ℂ)-(m:ℂ)=(s-(m:ℂ))+(n:ℂ) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hp),Complex.cpow_natCast]

theorem parameter_norm (p m : ℕ) (hp : 0<p) (s : ℂ) :
    ‖parameter p m s‖=(p:ℝ)^(s.re-(m:ℝ)) := by
  simp only [parameter,Complex.norm_natCast_cpow_of_pos hp,Complex.sub_re,
    Complex.natCast_re]

theorem real_part_of_parameter_two_norm (m : ℕ) (s : ℂ)
    (h : ‖parameter 2 m s‖=1) : s.re=m := by
  rw [parameter_norm 2 m (by decide)] at h
  have he : (2:ℝ)^(s.re-(m:ℝ))=(2:ℝ)^(0:ℝ) := by simpa using h
  have hz := (Real.rpow_right_inj (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp he
  linarith

theorem parameter_norm_add_nat (p m : ℕ) (hp : 0<p) (s : ℂ)
    (hs : s.re=m) (n : ℕ) : ‖parameter p m (s+n)‖=(p:ℝ)^n := by
  rw [parameter_norm p m hp]
  simp [hs]

theorem parameter_three_square_norm (m : ℕ) (s : ℂ) (hs : s.re=m) (n : ℕ) :
    ‖parameter 3 m (s+n)^2‖=(9:ℝ)^n := by
  rw [norm_pow,parameter_norm_add_nat 3 m (by decide) s hs n,
    ←pow_mul,mul_comm n 2,pow_mul]
  norm_num

#print axioms parameter_add_nat
#print axioms real_part_of_parameter_two_norm
#print axioms parameter_norm_add_nat
#print axioms parameter_three_square_norm
end SmallLevelPrimeRates
end
end

/-! ## SmallLevelTwentySixIntegerRatesV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelPrimeRates
open Complex

theorem parameter_nat_add (p m n : ℕ) :
    parameter p m ((m+n:ℕ):ℂ)=(p:ℂ)^n := by
  simp [parameter,Complex.cpow_natCast]

#print axioms parameter_nat_add
end SmallLevelPrimeRates
end
end
