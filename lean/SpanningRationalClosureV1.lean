module

public import SpanningAdditionIntegerSystemV1
public import SpanningTwoInjectionsClosureV1

@[expose] public section

namespace SpanningRationalClosure

open SpanningAdditionIntegerSystem SpanningIntegerRows SpanningActualKernel
  SpanningSlicedAddition GridAdmissibleGap

theorem two_rational_injections_force_zero {N B c d:ℕ} {L:Set ℕ}
    (hN:Admissible N) (hB:0<B) (hc:2≤c) (hd:2≤d)
    (hi:IndependentBases.Independent c d)
    (hcN:Nat.Coprime N c) (hdN:Nat.Coprime N d) (hdiv:∀ell∈L,ell∣B)
    (hci:AdditionInjective c B {f:ℤ → ℚ | Augmented N L B f})
    (hdi:AdditionInjective d B {f:ℤ → ℚ | Augmented N L B f}) :
    ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → ℚ,Augmented N L Q f → f=0 := by
  obtain ⟨Dc,_,hpc⟩ := addition_injective_mod_large_primes (by omega) hB hci
  obtain ⟨Dd,_,hpd⟩ := addition_injective_mod_large_primes (by omega) hB hdi
  obtain ⟨p,hlarge,hprime⟩ := Nat.exists_infinite_primes (Dc+Dd+1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨Q,hQ,hBQ,hzero⟩ :=
    SpanningTwoInjectionsClosure.two_injections_force_zero hN hB hc hd hi hcN hdN hdiv
      (hpc p hprime (by omega)) (hpd p hprime (by omega))
  exact ⟨Q,hQ,hBQ,augmented_zero_finite_field_rational hQ p hzero⟩

#print axioms two_rational_injections_force_zero

end SpanningRationalClosure
