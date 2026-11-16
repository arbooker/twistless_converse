module

public import QuantitativeMaassExactDivisorArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- Closure under products of disjoint exact divisors reduces every
squarefree exact divisor to the simple-prime cases. -/
theorem squarefree_exact_predicate (N : ℕ) (hN : 0<N) (F : ℕ → Prop)
    (h1 : F 1)
    (hmul : ∀ P Q D : ℕ,0<P → 0<Q → Nat.Coprime P Q → Nat.Coprime (P*Q) D →
      (P*Q)*D=N → F P → F Q → F (P*Q))
    (hp : ∀ p∈AsymptoticSectorSigns.simplePrimes N,F p)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) (hsq : Squarefree Q) : F Q := by
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
    exact hmul p R D hpprime.pos hR hs.1 hcop hQD (hp p hpN)
      (ih R hRQ (p*D) (by nlinarith [hQD]) hcR hs.2.2)

/-- At admissible levels each exact divisor or its complement is
squarefree. Product and cancellation closure therefore suffice. -/
theorem admissible_exact_predicate (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (F : ℕ → Prop) (h1 : F 1) (hfull : F N)
    (hmul : ∀ P Q D : ℕ,0<P → 0<Q → Nat.Coprime P Q → Nat.Coprime (P*Q) D →
      (P*Q)*D=N → F P → F Q → F (P*Q))
    (hcancel : ∀ P Q : ℕ,0<P → 0<Q → Nat.Coprime P Q → P*Q=N → F N → F Q → F P)
    (hp : ∀ p∈AsymptoticSectorSigns.simplePrimes N,F p)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) : F Q := by
  rcases admissible_exact_factor_squarefree N D Q hN hQD hcop with hs|hs
  · exact squarefree_exact_predicate N hN.1 F h1 hmul hp Q D hQD hcop hs
  · have hd := squarefree_exact_predicate N hN.1 F h1 hmul hp D Q
      (by nlinarith [hQD]) hcop.symm hs
    have hQ : 0<Q := by nlinarith [hN.1]
    have hD : 0<D := by nlinarith [hN.1]
    exact hcancel Q D hQ hD hcop hQD hfull hd

#print axioms squarefree_exact_predicate
#print axioms admissible_exact_predicate
end QuantitativeMaass
