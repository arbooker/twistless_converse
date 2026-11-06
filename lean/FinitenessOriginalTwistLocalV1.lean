module

public import FinitenessEulerIdentificationV1
public import FinitenessEulerTwistReciprocityV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalTwistLocal

open Complex FinitenessOriginalInput FinitenessEulerIdentification FinitenessEulerCoefficients
  FinitenessEulerLocal FinitenessRamanujanSum FinitenessEulerTwistLocal FinitenessEulerTwistReciprocity

noncomputable def D (N : ℕ) (f : ℕ → ℂ) (p j : ℕ) (z : ℂ) : ℂ :=
  polynomial p j (f p) (xi N p) z

/-- The finite multiplier belongs to the ACTUAL original sequence. -/
theorem local_series_polynomial {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (j : ℕ) {z : ℂ} (hz : (‖(f p:ℂ)‖+1)*‖z‖<1) :
    (1-(f p:ℂ)*z+xi N p*z^2)*
      (∑' t : ℕ, (f (p^t):ℂ)*complexSum (p^(j+1)) (p^t)*z^t)=D N f p j z := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have he (t : ℕ) : (f (p^t):ℂ)=coeff (f p) (xi N p) t :=
    (congr_fun (eq_canonical hf.zero hg hf.euler) (p^t)).trans (value_prime_pow _ _ hp t)
  have hs : (∑' t : ℕ, (f (p^t):ℂ)*complexSum (p^(j+1)) (p^t)*z^t)=
      localSeries p j (f p) (xi N p) z := tsum_congr (fun t => by rw [he t])
  rw [hs]
  exact local_polynomial hp j (f p) (xi N p) z (xi_bound N p) hz

theorem bad_parameter_zero {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpsq : p^2 ∣ N) : f p=0 := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by norm_num : 2≠0)) hpsq
  have h := hf.bad p hp hpN
  rw [ite_eq_left hpsq] at h
  exact eq_zero_of_pow_eq_zero h

theorem bad_parameter_simple {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬p^2 ∣ N) :
    (p:ℂ)*(f p)^2=1 := by
  have h := hf.bad p hp hpN
  rw [ite_eq_right hpsq] at h
  rw [h,mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero)]

theorem bad_root_sign {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬p^2 ∣ N) :
    -f p*Real.sqrt p=1 ∨ -f p*Real.sqrt p= -1 := by
  have H := bad_parameter_simple hf hp hpN hpsq
  have hs : (-f p*Real.sqrt p)^2=1 := by
    have hsqrt : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p)
    rw [mul_pow, neg_sq, hsqrt, mul_comm]
    exact H
  exact sq_eq_one_iff.mp hs

theorem good_reciprocal {N : ℕ} (f : ℕ → ℂ) {p : ℕ} (hp : 0<p)
    (hpN : ¬p ∣ N) (j : ℕ) {z : ℂ} (hz : z≠0) :
    D N f p j z=(p:ℂ)^(j+1)*z^(2*(j+1))*D N f p j (((p:ℂ)*z)⁻¹) := by
  simp only [D,xi,ite_eq_right hpN]
  exact good_reciprocity hp j (f p) hz

theorem bad_reciprocal {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬p^2 ∣ N)
    (j : ℕ) {z : ℂ} (hz : z≠0) :
    D N f p j z=(-(f p:ℂ))*(p:ℂ)^(j+1)*z^(2*j+1)*D N f p j (((p:ℂ)*z)⁻¹) := by
  simp only [D,xi,ite_eq_left hpN]
  apply bad_reciprocity hp.pos j (f p) hz
  exact bad_parameter_simple hf hp hpN hpsq

theorem square_bad {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpsq : p^2 ∣ N) (z : ℂ) :
    D N f p 0 z= -1 ∧ ∀ j, D N f p (j+1) z=0 := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by norm_num : 2≠0)) hpsq
  simp only [D,xi,ite_eq_left hpN,bad_parameter_zero hf hp hpsq]
  exact ⟨zero_bad_polynomial p z,fun j => zero_bad_polynomial_succ p j z⟩

#print axioms local_series_polynomial
#print axioms bad_root_sign
#print axioms bad_reciprocal
#print axioms square_bad

end FinitenessOriginalTwistLocal
