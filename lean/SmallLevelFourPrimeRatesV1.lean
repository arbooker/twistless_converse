module
public import SmallLevelPrimeRatesTheoryV4
public import Mathlib.LinearAlgebra.Vandermonde
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace SmallLevelFourPrimeRates
open Complex SmallLevelPrimeRates

def monomial (e : ℤ×ℤ×ℤ×ℤ) (x y z w : ℂ) : ℂ := x^e.1*y^e.2.1*z^e.2.2.1*w^e.2.2.2

theorem rational_power (p q r t : ℕ) (hp : 0<p) (hq : 0<q) (hr : 0<r) (ht : 0<t)
    (b : ℚ) (e : ℤ×ℤ×ℤ×ℤ)
    (hb : b=(p:ℚ)^e.1*(q:ℚ)^e.2.1*(r:ℚ)^e.2.2.1*(t:ℚ)^e.2.2.2)
    (s : ℂ) : (b:ℂ)^s=monomial e ((p:ℂ)^s) ((q:ℂ)^s) ((r:ℂ)^s) ((t:ℂ)^s) := by
  have hp' : (0:ℝ)<p:=by exact_mod_cast hp
  have hq' : (0:ℝ)<q:=by exact_mod_cast hq
  have hr' : (0:ℝ)<r:=by exact_mod_cast hr
  have ht' : (0:ℝ)<t:=by exact_mod_cast ht
  have hreal : (b:ℝ)=(p:ℝ)^e.1*(q:ℝ)^e.2.1*(r:ℝ)^e.2.2.1*(t:ℝ)^e.2.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_natCast] using congrArg (fun x : ℚ => (x:ℝ)) hb
  have hc : (b:ℂ)=(((p:ℝ)^e.1*(q:ℝ)^e.2.1*(r:ℝ)^e.2.2.1*(t:ℝ)^e.2.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun x : ℝ => (x:ℂ)) hreal
  rw [hc,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow_direct hp',positive_zpow_cpow_direct hq',
    positive_zpow_cpow_direct hr',positive_zpow_cpow_direct ht']
  simp only [Complex.ofReal_natCast,monomial]

/-- A finite collection of distinct rational rates detects every nonzero
coefficient vector at one of finitely many integer points. -/
theorem finite_power_sum_nonzero {n : ℕ} (b : Fin n→ℚ) (hb : Function.Injective b)
    (c : Fin n→ℂ) (i : Fin n) (hi : c i≠0) :
    ∃ j : Fin n,(∑ l : Fin n,c l*(b l:ℂ)^(j:ℕ))≠0 := by
  by_contra h
  push Not at h
  have hb' : Function.Injective (fun l : Fin n => (b l:ℂ)) := by
    intro l k h
    apply hb
    change (b l:ℂ)=(b k:ℂ) at h
    exact_mod_cast h
  have hc:=Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hb' h
  apply hi
  exact congrFun hc i

/-- The same finite test applies to a shifted complex-exponential sum,
so arbitrary auxiliary Hecke coefficients need not be divided out. -/
theorem exponential_sum_nonzero {n : ℕ} (b : Fin n→ℚ) (hb : Function.Injective b)
    (c : Fin n→ℂ) (i : Fin n) (hi : c i≠0) (m : ℕ) :
    ∃ s : ℂ,(∑ l : Fin n,c l*(b l:ℂ)^(s-(m:ℂ)))≠0 := by
  obtain ⟨j,hj⟩:=finite_power_sum_nonzero b hb c i hi
  refine ⟨(m:ℂ)+(j:ℕ),?_⟩
  simpa only [add_sub_cancel_left,Complex.cpow_natCast] using hj

#print axioms rational_power
#print axioms finite_power_sum_nonzero
#print axioms exponential_sum_nonzero
end SmallLevelFourPrimeRates
