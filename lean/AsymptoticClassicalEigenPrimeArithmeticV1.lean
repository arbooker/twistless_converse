module

public import AsymptoticClassicalEigenPrimeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

/-- The prime Hecke relation at n=1 identifies the eigenvalue with the
prime coefficient once a1 is normalized to one. -/
theorem prime_eigenvalue_eq_coefficient (a : ℕ → ℂ) (e b : Nat.Primes → ℂ)
    (hone : a 1 = 1)
    (hrec : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) = e p * a n - b p * (if p.val ∣ n then a (n/p.val) else 0))
    (p : Nat.Primes) : e p = a p.val := by
  have h := hrec p 1
  simpa [hone, p.property.not_dvd_one] using h.symm

/-- The full prime coefficient relation implies coprime multiplicativity
by strong induction on the first argument. No composite-index Hecke
operators are used. -/
theorem multiplicative_of_prime_recurrence (a : ℕ → ℂ) (b : Nat.Primes → ℂ)
    (hzero : a 0 = 0) (hone : a 1 = 1)
    (hrec : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) = a p.val * a n - b p * (if p.val ∣ n then a (n/p.val) else 0)) :
    ∀ m n : ℕ, m.Coprime n → a (m*n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro n hcop
    by_cases hm0 : m = 0
    · simp [hm0, hzero]
    by_cases hm1 : m = 1
    · simp [hm1, hone]
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hlt : m/p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hlt' : (m/p)/p < m := (Nat.div_le_self (m/p) p).trans_lt hlt
    have hrm : m/p ∣ m := Nat.div_dvd_of_dvd hpm
    have hrn : (m/p).Coprime n := hcop.coprime_dvd_left hrm
    have hpn : ¬p ∣ n := hp.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hpm)
    have hmrec := hrec (⟨p,hp⟩ : Nat.Primes) (m/p)
    simp only at hmrec
    rw [Nat.mul_div_cancel' hpm] at hmrec
    have hprod : m*n = p*((m/p)*n) := by rw [← mul_assoc, Nat.mul_div_cancel' hpm]
    rw [hprod, hrec (⟨p,hp⟩ : Nat.Primes) ((m/p)*n), ih (m/p) hlt n hrn, hmrec]
    by_cases hpr : p ∣ m/p
    · have hprn : p ∣ m/p*n := dvd_mul_of_dvd_left hpr n
      rw [ite_eq_left hprn, ite_eq_left hpr]
      have hdiv : (m/p*n)/p = ((m/p)/p)*n := by
        simpa only [mul_comm] using Nat.mul_div_assoc n hpr
      rw [hdiv, ih ((m/p)/p) hlt' n
        (hcop.coprime_dvd_left ((Nat.div_dvd_of_dvd hpr).trans hrm))]
      ring
    · have hprn : ¬p ∣ m/p*n := fun h => (hp.dvd_mul.mp h).elim hpr hpn
      rw [ite_eq_right hprn, ite_eq_right hpr]
      ring

/-- The same prime relation specializes to the required prime-power
quadratic recurrence. -/
theorem prime_power_of_prime_recurrence (a : ℕ → ℂ) (b : Nat.Primes → ℂ)
    (hrec : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) = a p.val * a n - b p * (if p.val ∣ n then a (n/p.val) else 0))
    (p : Nat.Primes) (j : ℕ) :
    a (p.val^(j+2)) = a p.val * a (p.val^(j+1)) - b p * a (p.val^j) := by
  have hpdiv : p.val ∣ p.val^(j+1) := dvd_pow_self _ (by omega)
  have h := hrec p (p.val^(j+1))
  rw [ite_eq_left hpdiv] at h
  have hdiv : p.val^(j+1)/p.val = p.val^j := by
    rw [pow_succ, Nat.mul_div_cancel _ p.property.pos]
  rw [hdiv, ← pow_succ'] at h
  exact h

#print axioms prime_eigenvalue_eq_coefficient
#print axioms multiplicative_of_prime_recurrence
#print axioms prime_power_of_prime_recurrence

end AsymptoticClassicalEigenbasis
