module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

public section

namespace FinitenessEulerRecurrence

variable {K : Type*} [Field K]

theorem full_recurrence (f beta : ℕ → K) (hf0 : f 0 = 0)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m*f n)
    (hrec : ∀ p, p.Prime → ∀ j,
      f (p^(j+2)) = f p*f (p^(j+1))-beta p*f (p^j))
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    f (p*n)+(if p ∣ n then beta p else 0)*f (n/p)=f p*f n := by
  by_cases hn : n=0
  · simp [hn, hf0]
  obtain ⟨e,r,hr,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hc : p.Coprime r := hp.coprime_iff_not_dvd.mpr hr
  cases e with
  | zero => simp only [pow_zero, one_mul, ite_eq_right hr, zero_mul, add_zero]; exact hmul p r hc
  | succ j =>
      have hd : p ∣ p^(j+1)*r := by
        exact ⟨p^j*r, by simp only [pow_succ', mul_assoc]⟩
      have hdiv : (p^(j+1)*r)/p = p^j*r := by
        rw [pow_succ', mul_assoc, Nat.mul_div_right _ hp.pos]
      have hprod : p*(p^(j+1)*r)=p^(j+2)*r := by
        rw [pow_succ' p (j+1), mul_assoc]
      rw [ite_eq_left hd, hdiv, hprod, hmul _ _ (hc.pow_left _),
        hmul _ _ (hc.pow_left _), hmul _ _ (hc.pow_left _), hrec p hp j]
      simp only [sub_mul, mul_assoc, sub_add_cancel]

theorem eq_of_prime_eq (f g beta : ℕ → K)
    (hf0 : f 0=0) (hg0 : g 0=0) (hf1 : f 1=1) (hg1 : g 1=1)
    (hfm : ∀ m n, m.Coprime n → f (m*n)=f m*f n)
    (hgm : ∀ m n, m.Coprime n → g (m*n)=g m*g n)
    (hfr : ∀ p, p.Prime → ∀ j,
      f (p^(j+2))=f p*f (p^(j+1))-beta p*f (p^j))
    (hgr : ∀ p, p.Prime → ∀ j,
      g (p^(j+2))=g p*g (p^(j+1))-beta p*g (p^j))
    (he : ∀ p, p.Prime → f p=g p) : f=g := by
  funext n
  refine Nat.recOnPrimeCoprime (by rw [hf0,hg0]) ?_ ?_ n
  · intro p j hp
    induction j using Nat.twoStepInduction with
    | zero => simpa using hf1.trans hg1.symm
    | one => simpa using he p hp
    | more j ih ih' => rw [hfr p hp j, hgr p hp j, ih, ih', he p hp]
  · intro a b _ _ hc ha hb
    rw [hfm a b hc, hgm a b hc, ha, hb]

#print axioms full_recurrence
#print axioms eq_of_prime_eq

end FinitenessEulerRecurrence
