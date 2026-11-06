module

public import FinitenessPrimeSeriesSplitV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessTwistedPrimeFactor

open Complex FinitenessRamanujanSum FinitenessRamanujanArithmetic FinitenessPrimeSeriesSplit
  FinitenessOriginalInput FinitenessEulerIdentification FinitenessEulerCoefficients
  FinitenessEulerLocal FinitenessEulerTwistLocal FinitenessOriginalTwistLocal

noncomputable def twistCoefficients (f : ℕ → ℂ) (q n : ℕ) : ℂ := f n*complexSum q n

noncomputable def restrictedSeries (p : ℕ) (f : ℕ → ℂ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑' m : CoprimePart p, f m.val*complexSum r m.val*(m.val:ℂ)^(-s)

theorem term_formula {f : ℕ → ℂ} (hf0 : f 0=0) (q : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (twistCoefficients f q) s n=f n*complexSum q n*(n:ℂ)^(-s) :=
  LSeries.term_def₀ (by simp [twistCoefficients,hf0]) s n

theorem weight_mul (p e m : ℕ) (s : ℂ) :
    ((p^e*m:ℕ):ℂ)^(-s)=((p:ℂ)^(-s))^e*(m:ℂ)^(-s) := by
  have H := mul_cpow_ofReal_nonneg (Nat.cast_nonneg (p^e) : (0:ℝ)≤((p^e:ℕ):ℝ))
    (Nat.cast_nonneg m : (0:ℝ)≤m) (-s)
  simp only [ofReal_natCast] at H
  rw [Nat.cast_mul,H,Nat.cast_pow,← natCast_cpow_natCast_mul,cpow_nat_mul]

/-- Separating one prime from the twisted series. This is valid even when
the local twisted series has zero constant term or vanishes identically. -/
theorem split_prime {p : ℕ} (hp : p.Prime) {r : ℕ} (hpr : p.Coprime r)
    (α : ℕ) {f : ℕ → ℂ} (hf0 : f 0=0)
    (hm : ∀ m n, m.Coprime n → f (m*n)=f m*f n) (s : ℂ)
    (hs : LSeriesSummable (twistCoefficients f (p^α*r)) s) :
    LSeries (twistCoefficients f (p^α*r)) s=
      (∑' e : ℕ, f (p^e)*complexSum (p^α) (p^e)*((p:ℂ)^(-s))^e)*
        restrictedSeries p f r s := by
  apply separated_sum hp (LSeries.term_zero _ _) hs
    (fun e => f (p^e)*complexSum (p^α) (p^e)*((p:ℂ)^(-s))^e)
    (fun m => f m.val*complexSum r m.val*(m.val:ℂ)^(-s))
  intro e m
  rw [term_formula hf0,hm _ _ (m.property.2.pow_left e),
    FinitenessRamanujanArithmetic.multiplicative (hpr.pow_left α),
    unit_invariance (m.property.2.pow_left α),weight_mul]
  have Hr : complexSum r (p^e*m.val)=complexSum r m.val := by
    rw [Nat.mul_comm]
    exact unit_invariance (hpr.symm.pow_right e) _
  rw [Hr]
  ring

theorem denominator_series (a b z : ℂ) (hb : ‖b‖≤1)
    (hz : (‖a‖+1)*‖z‖<1) : (1-a*z+b*z^2)*series a b z 0=1 := by
  have h0 := series_step a b z hb hz 0
  have h1 := series_step a b z hb hz 1
  have h2 := series_recurrence a b z hb hz
  simp only [coeff] at h0 h1
  linear_combination (1-a*z)*h0+z*h1+z^2*h2

/-- The actual local twist multiplier can be inserted one prime at a time.
No division by a possibly zero twisted local factor is used. -/
theorem prime_factor_step {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p r : ℕ} (hp : p.Prime) (hpr : p.Coprime r) (j : ℕ) (s : ℂ)
    (hz : (‖(f p:ℂ)‖+1)*‖(p:ℂ)^(-s)‖<1)
    (hr : LSeriesSummable (twistCoefficients f r) s)
    (hq : LSeriesSummable (twistCoefficients f (p^(j+1)*r)) s) :
    LSeries (twistCoefficients f (p^(j+1)*r)) s=
      D N f p j ((p:ℂ)^(-s))*LSeries (twistCoefficients f r) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hf0 : (f 0:ℂ)=0 := by simp [hf.zero]
  have hm : ∀ m n, m.Coprime n → (f (m*n):ℂ)=(f m:ℂ)*(f n:ℂ) := by
    intro m n hc
    exact_mod_cast FinitenessEulerIdentification.multiplicative hf.zero hg hf.euler hc
  have he (t : ℕ) : (f (p^t):ℂ)=coeff (f p) (xi N p) t :=
    (congr_fun (eq_canonical hf.zero hg hf.euler) (p^t)).trans (value_prime_pow _ _ hp t)
  have Hq := split_prime hp hpr (j+1) hf0 hm s hq
  have Hr := split_prime hp hpr 0 hf0 hm s (by simpa using hr)
  have heq : (∑' e : ℕ, (f (p^e):ℂ)*complexSum (p^(j+1)) (p^e)*((p:ℂ)^(-s))^e)=
      localSeries p j (f p) (xi N p) ((p:ℂ)^(-s)) :=
    tsum_congr (fun e => by rw [he e])
  rw [heq] at Hq
  have her : (∑' e : ℕ, (f (p^e):ℂ)*complexSum (p^0) (p^e)*((p:ℂ)^(-s))^e)=
      series (f p) (xi N p) ((p:ℂ)^(-s)) 0 := by
    have hone (n : ℕ) : complexSum 1 n=1 := by simp [complexSum,residues,phase]
    unfold series
    apply tsum_congr
    intro e
    simp only [pow_zero,hone,mul_one,Nat.add_zero]
    exact congrArg (fun t => t*((p:ℂ)^(-s))^e) (he e)
  rw [her] at Hr
  simp only [pow_zero,one_mul] at Hr
  rw [Hq,Hr]
  have H0 := denominator_series (f p) (xi N p) ((p:ℂ)^(-s)) (xi_bound N p) hz
  have H1 := local_polynomial hp j (f p) (xi N p) ((p:ℂ)^(-s)) (xi_bound N p) hz
  unfold D
  linear_combination
    -(localSeries p j (f p) (xi N p) ((p:ℂ)^(-s))*restrictedSeries p f r s)*H0+
    (series (f p) (xi N p) ((p:ℂ)^(-s)) 0*restrictedSeries p f r s)*H1

#print axioms split_prime
#print axioms prime_factor_step

end FinitenessTwistedPrimeFactor
