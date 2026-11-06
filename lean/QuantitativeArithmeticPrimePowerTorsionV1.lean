module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticPrimePowerTorsion
open Complex

theorem distinct_primes_zpow_independent {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (a b : ℤ) (h : (p:ℝ)^a*(q:ℝ)^b=1) : a=0 ∧ b=0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q:ℚ)≠0 := by exact_mod_cast hq.ne_zero
  have hr : (p:ℚ)^a*(q:ℚ)^b=1 := by
    apply Rat.cast_injective (α:=ℝ)
    push_cast
    exact h
  have h1 := congrArg (padicValRat p) hr
  have h2 := congrArg (padicValRat q) hr
  rw [padicValRat.mul (zpow_ne_zero _ hp0) (zpow_ne_zero _ hq0),
    padicValRat.zpow,padicValRat.zpow,padicValRat.self hp.one_lt,
    padicValRat.of_nat,padicValNat_primes hpq,padicValRat.one] at h1
  rw [padicValRat.mul (zpow_ne_zero _ hp0) (zpow_ne_zero _ hq0),
    padicValRat.zpow,padicValRat.zpow,padicValRat.self hq.one_lt,
    padicValRat.of_nat,padicValNat_primes hpq.symm,padicValRat.one] at h2
  constructor
  · simpa using h1
  · simpa using h2

/-- Two distinct positive primes have no common nonzero complex exponent
for which both powers equal one. -/
theorem distinct_primes_cpow_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u : ℂ) (hpu : (p:ℂ)^u=1) (hqu : (q:ℂ)^u=1) : u=0 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast hq.ne_zero
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hqR : 0<(q:ℝ) := by exact_mod_cast hq.pos
  rw [Complex.cpow_def_of_ne_zero hp0] at hpu
  rw [Complex.cpow_def_of_ne_zero hq0] at hqu
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp hpu
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp hqu
  have hlp : Complex.log (p:ℂ)=(Real.log (p:ℝ):ℂ) := by
    simp
  have hlq : Complex.log (q:ℂ)=(Real.log (q:ℝ):ℂ) := by
    simp
  rw [hlp] at hn
  rw [hlq] at hm
  have hT : (2*(Real.pi:ℂ)*I)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have he : ((Real.log (q:ℝ):ℂ)*(n:ℂ)-(Real.log (p:ℝ):ℂ)*(m:ℂ))*
      (2*(Real.pi:ℂ)*I)=0 := by
    linear_combination (Real.log (p:ℝ):ℂ)*hm-(Real.log (q:ℝ):ℂ)*hn
  have hr : Real.log (q:ℝ)*(n:ℝ)-Real.log (p:ℝ)*(m:ℝ)=0 := by
    exact_mod_cast (mul_eq_zero.mp he).resolve_right hT
  have hpos : 0<(p:ℝ)^(-m)*(q:ℝ)^n := mul_pos (zpow_pos hpR _) (zpow_pos hqR _)
  have hlog : Real.log ((p:ℝ)^(-m)*(q:ℝ)^n)=0 := by
    rw [Real.log_mul (zpow_ne_zero _ hpR.ne') (zpow_ne_zero _ hqR.ne'),
      Real.log_zpow,Real.log_zpow]
    push_cast
    linear_combination hr
  have hprod : (p:ℝ)^(-m)*(q:ℝ)^n=1 := by
    rw [← Real.exp_log hpos,hlog,Real.exp_zero]
  obtain ⟨_,hn0⟩ := distinct_primes_zpow_independent hp hq hpq (-m) n hprod
  have hlp0 : (Real.log (p:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))
  rw [hn0] at hn
  simp only [Int.cast_zero,zero_mul] at hn
  exact (mul_eq_zero.mp hn).resolve_left hlp0

/-- A common complex exponent cannot give roots of unity at two distinct
primes unless the exponent is zero. -/
theorem distinct_primes_cpow_torsion {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (u : ℂ) (r t : ℕ) (hr : 0<r) (ht : 0<t)
    (hpu : ((p:ℂ)^u)^r=1) (hqu : ((q:ℂ)^u)^t=1) : u=0 := by
  have hp' : (p:ℂ)^((r*t:ℕ)*u)=1 := by
    rw [Complex.cpow_nat_mul,pow_mul,hpu,one_pow]
  have hq' : (q:ℂ)^((r*t:ℕ)*u)=1 := by
    rw [Complex.cpow_nat_mul,Nat.mul_comm r t,pow_mul,hqu,one_pow]
  have he := distinct_primes_cpow_one hp hq hpq ((r*t:ℕ)*u) hp' hq'
  have hn : ((r*t:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.mul_pos hr ht).ne'
  exact (mul_eq_zero.mp he).resolve_left hn

#print axioms distinct_primes_zpow_independent
#print axioms distinct_primes_cpow_one
#print axioms distinct_primes_cpow_torsion
end QuantitativeArithmeticPrimePowerTorsion
