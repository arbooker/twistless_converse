module

public import FinitenessOriginalTwistedContinuationsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRamifiedCoefficients

open FinitenessOriginalInput FinitenessOriginalFourier FinitenessEulerIdentification
open scoped BigOperators

/-- The root of a Ramanujan twist depends only on the simple ramified
primes common to q and N, with no dependence on their valuations in q. -/
theorem twist_root (N : ℕ) (f : ℕ → ℂ) (q : ℕ) :
    FinitenessNormalizedTwistProduct.root N f q=
      ∏ p ∈ q.primeFactors.filter (fun p => p∣N ∧ ¬p^2∣N), -(f p*(Real.sqrt p:ℂ)) := by
  classical
  rw [FinitenessNormalizedTwistProduct.root,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hfac : q.factorization p≠0 := by
    apply Finsupp.mem_support_iff.mp
    simpa only [Nat.support_factorization] using hp
  simp only [FinitenessNormalizedTwistLocal.sign,ite_eq_right hfac,neg_mul]

/-- At a ramified prime the literal Euler product implies the recurrence
at every index, including indices divisible by that prime. -/
theorem bad_mul {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) (n : ℕ) : f (p*n)=f p*f n := by
  by_cases hn : n=0
  · simp [hn,hf.zero]
  obtain ⟨τ,_,hg⟩ := hf.growth
  let j := n.factorization p
  let u := n/p^j
  have hc : p.Coprime u := Nat.coprime_ordCompl hp hn
  have hdecomp : p^j*u=n := Nat.ordProj_mul_ordCompl_eq_self n p
  calc
    f (p*n)=f (p^(j+1)*u) := by rw [pow_succ',mul_assoc,hdecomp]
    _ = f (p^(j+1))*f u := multiplicative hf.zero hg hf.euler (hc.pow_left (j+1))
    _ = f p*(f (p^j)*f u) := by
      rw [bad_prime_power hf.zero hg hf.euler hp hpN,
        bad_prime_power hf.zero hg hf.euler hp hpN,pow_succ']
      ring
    _ = f p*f n := by rw [← multiplicative hf.zero hg hf.euler (hc.pow_left j),hdecomp]

theorem fullCoefficients_bad_mul {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) (k n : ℕ) :
    fullCoefficients f k (p*n)=
      (f p*((p:ℝ)^FinitenessCompletedNormalization.alpha k:ℝ))*fullCoefficients f k n := by
  simp only [fullCoefficients,FinitenessGrowthNormalization.normalized,bad_mul hf hp hpN,
    Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg n),Complex.ofReal_mul]
  ring

/-- The sector sign is the actual normalized ramified Euler coefficient. -/
theorem simple_sign {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) (hpsq : ¬p^2∣N) :
    f p*(Real.sqrt p:ℂ)=1 ∨ f p*(Real.sqrt p:ℂ)= -1 := by
  rcases FinitenessOriginalTwistLocal.bad_root_sign hf hp hpN hpsq with hh | hh
  · right
    linear_combination -hh
  · left
    linear_combination -hh

/-- In weight k=2h+2 the simple-ramified relation is precisely
a_(pn)=delta_p p^h a_n, with delta_p=f_p sqrt(p). -/
theorem simple_relation {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) (h n : ℕ) :
    fullCoefficients f (2*(h+1)) (p*n)=
      (f p*(Real.sqrt p:ℂ))*(p:ℂ)^h*fullCoefficients f (2*(h+1)) n := by
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have he : (p:ℝ)^FinitenessCompletedNormalization.alpha (2*(h+1))=Real.sqrt p*(p:ℝ)^h := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_add hp']
    congr 1
    unfold FinitenessCompletedNormalization.alpha
    push_cast
    ring
  rw [fullCoefficients_bad_mul hf hp hpN,he]
  push_cast
  ring

/-- Square-ramified Euler factors force the whole p-divisible row to
vanish, not just its first coefficient. -/
theorem square_relation {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpsq : p^2∣N) (k n : ℕ) :
    fullCoefficients f k (p*n)=0 := by
  have hpN : p∣N := dvd_trans (dvd_pow_self p (by omega : 2≠0)) hpsq
  rw [fullCoefficients_bad_mul hf hp hpN,
    FinitenessOriginalTwistLocal.bad_parameter_zero hf hp hpsq,zero_mul,zero_mul]

#print axioms bad_mul
#print axioms twist_root
#print axioms simple_sign
#print axioms simple_relation
#print axioms square_relation

end AsymptoticRamifiedCoefficients
