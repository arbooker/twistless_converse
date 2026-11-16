module

public import QuantitativeMaassExactDivisorArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- Arithmetic induction for functions whose exact-divisor product law
has been established separately. -/
theorem squarefree_exact_character_eq (N : ℕ) (hN : 0<N) (f g : ℕ→ℂ)
    (h1 : f 1=g 1)
    (hf : ∀ P Q D : ℕ,0<P→0<Q→Nat.Coprime P Q→Nat.Coprime (P*Q) D→
      (P*Q)*D=N→f P*f Q=f (P*Q))
    (hg : ∀ P Q D : ℕ,0<P→0<Q→Nat.Coprime P Q→Nat.Coprime (P*Q) D→
      (P*Q)*D=N→g P*g Q=g (P*Q))
    (hp : ∀ p∈AsymptoticSectorSigns.simplePrimes N,f p=g p)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) (hsq : Squarefree Q) :
    f Q=g Q := by
  induction Q using Nat.strong_induction_on generalizing D with
  | h Q ih =>
    by_cases hQ1 : Q=1
    · simpa only [hQ1] using h1
    obtain ⟨p,hpprime,hpQ⟩ := Nat.exists_prime_and_dvd hQ1
    obtain ⟨R,hQR⟩ := hpQ
    have hQpos : 0<Q := by nlinarith
    have hR : 0<R := by nlinarith
    have hRQ : R<Q := by nlinarith [hpprime.two_le]
    have hpN := squarefree_exact_prime_simple N D Q p hQD hcop hsq hpprime ⟨R,hQR⟩
    subst Q
    have hs := Nat.squarefree_mul_iff.mp hsq
    have hcR : Nat.Coprime R (p*D) := hs.1.symm.mul_right (hcop.of_dvd_left (dvd_mul_left R p))
    have hr := ih R hRQ (p*D) (by nlinarith [hQD]) hcR hs.2.2
    rw [←hf p R D hpprime.pos hR hs.1 hcop hQD,
      ←hg p R D hpprime.pos hR hs.1 hcop hQD,hp p hpN,hr]

/-- At admissible levels the full-divisor value and the simple-prime
values determine every exact-divisor value of a nonvanishing character. -/
theorem admissible_exact_character_eq (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (f g : ℕ→ℂ) (h1 : f 1=g 1) (hfull : f N=g N)
    (hf : ∀ P Q D : ℕ,0<P→0<Q→Nat.Coprime P Q→Nat.Coprime (P*Q) D→
      (P*Q)*D=N→f P*f Q=f (P*Q))
    (hg : ∀ P Q D : ℕ,0<P→0<Q→Nat.Coprime P Q→Nat.Coprime (P*Q) D→
      (P*Q)*D=N→g P*g Q=g (P*Q))
    (hp : ∀ p∈AsymptoticSectorSigns.simplePrimes N,f p=g p)
    (hne : ∀ Q D : ℕ,Q*D=N→Nat.Coprime Q D→f Q≠0)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) : f Q=g Q := by
  rcases admissible_exact_factor_squarefree N D Q hN hQD hcop with hs|hs
  · exact squarefree_exact_character_eq N hN.1 f g h1 hf hg hp Q D hQD hcop hs
  · have hd := squarefree_exact_character_eq N hN.1 f g h1 hf hg hp D Q
      (by nlinarith [hQD]) hcop.symm hs
    have hQ : 0<Q := by nlinarith [hN.1]
    have hD : 0<D := by nlinarith [hN.1]
    have he : f Q*f D=g Q*f D := by
      rw [hf Q D 1 hQ hD hcop (Nat.coprime_one_right _) (by simpa using hQD),
        hd,hg Q D 1 hQ hD hcop (Nat.coprime_one_right _) (by simpa using hQD),hQD,hfull]
    exact mul_right_cancel₀ (hne D Q (by nlinarith [hQD]) hcop.symm) he

#print axioms squarefree_exact_character_eq
#print axioms admissible_exact_character_eq

end QuantitativeMaass
