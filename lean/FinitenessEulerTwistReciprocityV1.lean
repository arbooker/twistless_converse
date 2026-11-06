module

public import FinitenessEulerTwistLocalV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerTwistReciprocity

open Complex FinitenessEulerLocal FinitenessEulerTwistLocal

theorem reciprocal_product {p z : ℂ} (hp : p≠0) (hz : z≠0) :
    (p*z^2)*(p*z)⁻¹=z := by
  field_simp

theorem quadratic_reciprocity (A B : ℂ) {p z : ℂ} (hp : p≠0) (hz : z≠0) :
    p*z^2*(-A+B*(p*z)⁻¹-p*A*((p*z)⁻¹)^2)= -A+B*z-p*A*z^2 := by
  field_simp
  ring

theorem monomial_transport (A : ℂ) (j : ℕ) (F : ℂ → ℂ) {p z : ℂ}
    (hp : p≠0) (hz : z≠0) (c : ℂ) :
    ((p*z^2)^j*c)*(A*((p*z)⁻¹)^j*F ((p*z)⁻¹))=
      A*z^j*(c*F ((p*z)⁻¹)) := by
  calc
    _ = A*((p*z^2)*(p*z)⁻¹)^j*(c*F ((p*z)⁻¹)) := by rw [mul_pow]; ring
    _ = _ := by rw [reciprocal_product hp hz]

/-- Good-prime reciprocity, with z=p^(-s). The reflected variable is
(p*z)^(-1)=p^(-(1-s)); the factor is p^(alpha*(1-2s)). -/
theorem good_reciprocity {p : ℕ} (hp : 0<p) (j : ℕ) (a : ℂ) {z : ℂ} (hz : z≠0) :
    polynomial p j a 1 z=(p:ℂ)^(j+1)*z^(2*(j+1))*
      polynomial p j a 1 (((p:ℂ)*z)⁻¹) := by
  have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  let A := coeff a 1 j
  let B := a*coeff a 1 j+((p:ℂ)-1)*coeff a 1 (j+1)
  let F : ℂ → ℂ := fun w => -A+B*w-(p:ℂ)*A*w^2
  have H := monomial_transport ((p:ℂ)^j) j F hp' hz ((p:ℂ)*z^2)
  have Hq := quadratic_reciprocity A B hp' hz
  dsimp only [F] at H
  rw [Hq] at H
  have he : ((p:ℂ)*z^2)^j*((p:ℂ)*z^2)=(p:ℂ)^(j+1)*z^(2*(j+1)) := by
    rw [← pow_succ,mul_pow,pow_mul]
  rw [he] at H
  simpa only [polynomial,mul_one,A,B] using H.symm

theorem coeff_zero (a : ℂ) (j : ℕ) : coeff a 0 j=a^j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [coeff]
  | one => simp [coeff]
  | more j _ ih =>
      change a*coeff a 0 (j+1)-0*coeff a 0 j=a^(j+2)
      rw [zero_mul,sub_zero,ih]
      exact (pow_succ' a (j+1)).symm

theorem bad_polynomial (p j : ℕ) (a z : ℂ) :
    polynomial p j a 0 z=(p:ℂ)^j*a^j*z^j*(-1+(p:ℂ)*a*z) := by
  simp only [polynomial,coeff_zero,pow_succ,mul_zero,zero_mul,sub_zero]
  ring

theorem linear_reciprocity {p a z : ℂ} (hp : p≠0) (hz : z≠0) (ha : p*a^2=1) :
    (-a)*p*z*(-1+p*a*(p*z)⁻¹)= -1+p*a*z := by
  field_simp
  linear_combination -ha

/-- For a bad prime with p*a^2=1. The scalar equals
(-a*sqrt(p))*p^((2*alpha-1)*(1/2-s)) after z=p^(-s). -/
theorem bad_reciprocity {p : ℕ} (hp : 0<p) (j : ℕ) (a : ℂ)
    {z : ℂ} (hz : z≠0) (ha : (p:ℂ)*a^2=1) :
    polynomial p j a 0 z=(-a)*(p:ℂ)^(j+1)*z^(2*j+1)*
      polynomial p j a 0 (((p:ℂ)*z)⁻¹) := by
  have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  let F : ℂ → ℂ := fun w => -1+(p:ℂ)*a*w
  have H := monomial_transport ((p:ℂ)^j*a^j) j F hp' hz ((-a)*(p:ℂ)*z)
  dsimp only [F] at H
  rw [linear_reciprocity hp' hz ha] at H
  have he : ((p:ℂ)*z^2)^j*((-a)*(p:ℂ)*z)=(-a)*(p:ℂ)^(j+1)*z^(2*j+1) := by
    simp only [pow_add,pow_mul,mul_pow,pow_one,pow_two]
    ring
  rw [he] at H
  simpa only [bad_polynomial] using H.symm

/-- If p^2 divides N then the bad Euler parameter is zero: the twist
multiplier is -1 for alpha=1 and vanishes for every alpha>=2. -/
theorem zero_bad_polynomial (p : ℕ) (z : ℂ) : polynomial p 0 0 0 z= -1 := by
  simp [bad_polynomial]

theorem zero_bad_polynomial_succ (p j : ℕ) (z : ℂ) : polynomial p (j+1) 0 0 z=0 := by
  simp [bad_polynomial]

#print axioms good_reciprocity
#print axioms bad_reciprocity
#print axioms zero_bad_polynomial_succ

end FinitenessEulerTwistReciprocity
