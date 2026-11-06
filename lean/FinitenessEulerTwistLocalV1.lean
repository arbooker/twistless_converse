module

public import FinitenessRamanujanArithmeticV1
public import FinitenessEulerLocalV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerTwistLocal

open Complex Finset FinitenessRamanujanSum FinitenessRamanujanArithmetic FinitenessEulerLocal

theorem series_recurrence_shift (a b z : ℂ) (hb : ‖b‖≤1)
    (hz : (‖a‖+1)*‖z‖<1) (t : ℕ) :
    series a b z (t+2)=a*series a b z (t+1)-b*series a b z t := by
  unfold series
  rw [← tsum_mul_left,← tsum_mul_left,
    ← (summable_shift a b z hb hz (t+1) |>.mul_left a).tsum_sub
      (summable_shift a b z hb hz t |>.mul_left b)]
  apply tsum_congr
  intro n
  change coeff a b ((n+t)+2)*z^n=
    a*(coeff a b ((n+t)+1)*z^n)-b*(coeff a b (n+t)*z^n)
  rw [show coeff a b ((n+t)+2)=a*coeff a b ((n+t)+1)-b*coeff a b (n+t) from rfl]
  ring

theorem tail_numerator (a b z : ℂ) (hb : ‖b‖≤1)
    (hz : (‖a‖+1)*‖z‖<1) (j : ℕ) :
    (1-a*z+b*z^2)*series a b z (j+1)=coeff a b (j+1)-b*coeff a b j*z := by
  have h0 := series_step a b z hb hz (j+1)
  have h1 := series_step a b z hb hz (j+2)
  have h2 := series_recurrence_shift a b z hb hz (j+1)
  simp only [show j+1+1=j+2 by omega,show j+1+2=j+3 by omega] at h0 h1 h2
  rw [show coeff a b (j+2)=a*coeff a b (j+1)-b*coeff a b j from rfl] at h1
  linear_combination (1-a*z)*h0+z*h1+z^2*h2

noncomputable def localSeries (p j : ℕ) (a b z : ℂ) : ℂ :=
  ∑' t : ℕ, coeff a b t*complexSum (p^(j+1)) (p^t)*z^t

noncomputable def polynomial (p j : ℕ) (a b z : ℂ) : ℂ :=
  (p:ℂ)^j*z^j*(-coeff a b j+
    (a*coeff a b j+((p:ℂ)-1)*coeff a b (j+1))*z-(p:ℂ)*b*coeff a b j*z^2)

theorem local_summable (p j : ℕ) (a b z : ℂ) (hb : ‖b‖≤1)
    (hz : (‖a‖+1)*‖z‖<1) :
    Summable (fun t : ℕ => coeff a b t*complexSum (p^(j+1)) (p^t)*z^t) := by
  have hs : Summable (fun t : ℕ => ‖coeff a b t*z^t‖) := by
    simpa only [Nat.add_zero] using (summable_shift a b z hb hz 0).norm
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left ((p^(j+1):ℕ):ℝ))
  intro t
  have h := complexSum_bound (p^(j+1)) (p^t)
  simp only [norm_mul,norm_pow]
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (coeff a b t)),
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (norm_nonneg (coeff a b t)))
      (pow_nonneg (norm_nonneg z) t)]

theorem at_prime_power {p : ℕ} (hp : p.Prime) (j t : ℕ) :
    complexSum (p^(j+1)) (p^t)=
      (if j+1≤t then (p:ℂ)^(j+1) else 0)-(if j≤t then (p:ℂ)^j else 0) := by
  rw [prime_power hp]
  simp only [Nat.pow_dvd_pow_iff_le_right hp.one_lt,Nat.cast_pow]

theorem local_tail {p : ℕ} (hp : p.Prime) (j : ℕ) (a b z : ℂ)
    (hb : ‖b‖≤1) (hz : (‖a‖+1)*‖z‖<1) :
    localSeries p j a b z=(p:ℂ)^j*z^j*
      (-coeff a b j+((p:ℂ)-1)*z*series a b z (j+1)) := by
  have hs := local_summable p j a b z hb hz
  have hprefix : (∑ t ∈ range j, coeff a b t*complexSum (p^(j+1)) (p^t)*z^t)=0 := by
    apply sum_eq_zero
    intro t ht
    have ht' := mem_range.mp ht
    rw [at_prime_power hp]
    simp [show ¬j+1≤t by omega,show ¬j≤t by omega]
  unfold localSeries
  rw [← hs.sum_add_tsum_nat_add j,hprefix,zero_add,
    ((summable_nat_add_iff j).mpr hs).tsum_eq_zero_add]
  simp only [Nat.zero_add]
  rw [at_prime_power hp,ite_eq_right (by omega : ¬j+1≤j),ite_eq_left le_rfl]
  have htail : (∑' t : ℕ, coeff a b (t+1+j)*complexSum (p^(j+1)) (p^(t+1+j))*z^(t+1+j))=
      (p:ℂ)^j*((p:ℂ)-1)*z^(j+1)*series a b z (j+1) := by
    unfold series
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [at_prime_power hp,ite_eq_left (by omega : j+1≤t+1+j),
      ite_eq_left (by omega : j≤t+1+j)]
    simp only [show t+1+j=t+(j+1) by omega,pow_add,pow_one]
    ring
  rw [htail,pow_succ]
  ring

/-- The local Ramanujan-twisted series times the Euler denominator is
a finite polynomial. Its constant terms may vanish; no division by a
Ramanujan value or by a twisted local series is used. -/
theorem local_polynomial {p : ℕ} (hp : p.Prime) (j : ℕ) (a b z : ℂ)
    (hb : ‖b‖≤1) (hz : (‖a‖+1)*‖z‖<1) :
    (1-a*z+b*z^2)*localSeries p j a b z=polynomial p j a b z := by
  rw [local_tail hp j a b z hb hz]
  have H := tail_numerator a b z hb hz j
  unfold polynomial
  linear_combination (p:ℂ)^j*z^j*((p:ℂ)-1)*z*H

#print axioms local_tail
#print axioms local_polynomial

end FinitenessEulerTwistLocal
