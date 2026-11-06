module

public import AsymptoticClassicalEigenNormalizationV1
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

/-- A sequence satisfying the prime Hecke recurrences is determined by
its first coefficient. The proof uses strong induction, not operators T_n. -/
theorem zero_of_prime_recurrence (a : ℕ → ℂ) (e b : Nat.Primes → ℂ)
    (hzero : a 0 = 0) (hone : a 1 = 0)
    (hrec : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) = e p * a n - b p * (if p.val ∣ n then a (n/p.val) else 0)) :
    a = 0 := by
  funext n
  change a n = 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simpa only [hn0] using hzero
    by_cases hn1 : n = 1
    · simpa only [hn1] using hone
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hlt : n/p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp.one_lt
    have hlt' : (n/p)/p < n := (Nat.div_le_self (n/p) p).trans_lt hlt
    have H := hrec (⟨p, hp⟩ : Nat.Primes) (n/p)
    simp only at H
    rw [Nat.mul_div_cancel' hpn, ih (n/p) hlt, ih ((n/p)/p) hlt'] at H
    simpa using H

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The exact prime-operator coefficient law and Fourier separation
prove that a joint eigenvector with first coefficient zero vanishes. -/
theorem prime_joint_first_kernel (T : Nat.Primes → E →ₗ[ℂ] E)
    (coeff : ℕ → E →ₗ[ℂ] ℂ) (b : Nat.Primes → ℂ)
    (hzero : ∀ v, coeff 0 v = 0)
    (hsep : ∀ v, (∀ n, coeff n v = 0) → v = 0)
    (hcoeff : ∀ (p : Nat.Primes) (n : ℕ) (v : E),
      coeff n (T p v) = coeff (p.val*n) v +
        b p * (if p.val ∣ n then coeff (n/p.val) v else 0))
    {v : E} {e : Nat.Primes → ℂ} (heigen : ∀ p, T p v = e p • v)
    (hone : coeff 1 v = 0) : v = 0 := by
  have ha : (fun n => coeff n v) = 0 := by
    apply zero_of_prime_recurrence (fun n => coeff n v) e b (hzero v) hone
    intro p n
    have h := hcoeff p n v
    rw [heigen, map_smul, smul_eq_mul] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  apply hsep
  intro n
  exact congrFun ha n

#print axioms zero_of_prime_recurrence
#print axioms prime_joint_first_kernel

end AsymptoticClassicalEigenbasis
