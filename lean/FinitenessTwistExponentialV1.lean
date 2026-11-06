module

public import FinitenessTwistConductorV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessTwistExponential

open Complex

noncomputable def power (p : ℕ) (s : ℂ) : ℂ := exp ((Real.log p:ℂ)*s)

theorem power_eq {p : ℕ} (hp : 0<p) (s : ℂ) : power p s=(p:ℂ)^s := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  simp only [power,Complex.natCast_log]

theorem power_add (p : ℕ) (s t : ℂ) : power p (s+t)=power p s*power p t := by
  simp only [power,mul_add,exp_add]

theorem power_nat (p n : ℕ) : (power p (1:ℂ))^n=power p (n:ℂ) := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [pow_succ,ih,Nat.cast_add,Nat.cast_one,power_add]

theorem power_mul_nat (p : ℕ) (s : ℂ) (n : ℕ) : (power p s)^n=power p ((n:ℂ)*s) := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
      rw [pow_succ,ih,← power_add]
      congr 1
      push_cast
      ring

theorem power_one {p : ℕ} (hp : 0<p) : power p 1=(p:ℂ) := by
  rw [power_eq hp,cpow_one]

theorem power_nat_value {p : ℕ} (hp : 0<p) (n : ℕ) : power p (n:ℂ)=(p:ℂ)^n := by
  rw [← power_nat,power_one hp]

theorem power_half {p : ℕ} (hp : 0<p) : power p (1/2:ℂ)=(Real.sqrt p:ℂ) := by
  rw [power_eq hp,Real.sqrt_eq_rpow]
  simpa only [ofReal_div,ofReal_one,ofReal_ofNat,ofReal_natCast] using
    (Complex.ofReal_cpow (Nat.cast_nonneg p) (1/2:ℝ)).symm

theorem power_ne_zero (p : ℕ) (s : ℂ) : power p s≠0 := exp_ne_zero _

theorem reflected {p : ℕ} (hp : 0<p) (s : ℂ) :
    power p (-(1-s))=((p:ℂ)*power p (-s))⁻¹ := by
  rw [← power_one hp,← power_add]
  simp only [power]
  rw [← exp_neg]
  congr 1
  ring

theorem good_scalar {p : ℕ} (hp : 0<p) (j : ℕ) (s : ℂ) :
    (p:ℂ)^(j+1)*(power p (-s))^(2*(j+1))=
      power p ((2*((j:ℂ)+1))*(1/2-s)) := by
  rw [← power_nat_value hp,power_mul_nat,← power_add]
  congr 1
  push_cast
  ring

theorem bad_scalar {p : ℕ} (hp : 0<p) (j : ℕ) (a s : ℂ) :
    (-a)*(p:ℂ)^(j+1)*(power p (-s))^(2*j+1)=
      (-a*(Real.sqrt p:ℂ))*power p ((2*(j:ℂ)+1)*(1/2-s)) := by
  rw [← power_nat_value hp,power_mul_nat,← power_half hp]
  simp only [mul_assoc,← power_add]
  congr 2
  push_cast
  ring

noncomputable def scale (p β : ℕ) (s : ℂ) : ℂ :=
  power p ((β:ℂ)*(s-1/2)/2)

theorem scale_transport (p β : ℕ) (s : ℂ) :
    scale p β s*power p ((β:ℂ)*(1/2-s))=scale p β (1-s) := by
  unfold scale
  rw [← power_add]
  congr 1
  ring

theorem power_entire (p : ℕ) : Differentiable ℂ (power p) := by
  exact differentiable_exp.comp ((differentiable_const _).mul differentiable_id)

theorem scale_entire (p β : ℕ) : Differentiable ℂ (scale p β) := by
  exact (power_entire p).comp
    (((differentiable_const _).mul (differentiable_id.sub (differentiable_const _))).div_const _)

theorem power_bound (p : ℕ) : FinitenessFiniteOrder.Bound (power p) :=
  FinitenessFiniteOrder.exp_linear (Real.log p)

theorem scale_bound (p β : ℕ) : FinitenessFiniteOrder.Bound (scale p β) := by
  have h := FinitenessInputBounds.bound_shift
    (FinitenessFiniteOrder.exp_linear (Real.log p*(β:ℝ)/2)) (-1/2:ℂ)
  have he : scale p β=(fun z : ℂ => exp (((Real.log p*(β:ℝ)/2:ℝ):ℂ)*(z+(-1/2)))) := by
    funext z
    unfold scale power
    congr 1
    push_cast
    ring
  rw [he]
  exact h

#print axioms good_scalar
#print axioms bad_scalar
#print axioms scale_bound

end FinitenessTwistExponential
