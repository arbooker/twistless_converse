module

public import QuantitativeArithmeticRetainedConcentrationV1
public import SpanningClassicalConcentrationV1
public import SpanningStationaryTraceV1
public import SpanningAdditionIntegerSystemV1

@[expose] public section

namespace QuantitativeArithmeticRetainedClosure

open SpanningKernelDefects QuantitativeArithmeticRetainedConcentration SpanningActualKernel
  GridAdmissibleGap SpanningSlicedAddition

variable {K : Type} [Field K] [Finite K]

/-- The complete stationary/automatic/grid argument over a finite field:
two independent coprime addition injections imply an actual zero augmented
kernel at some multiple of the base. -/
theorem two_injections_force_zero {N B c d : ℕ} {L : Set ℕ}
    (hN : 0 < N) (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    (hSL : (S : Set ℕ) ⊆ L) (detector : GridDifferenceDetector K N S)
    (hB : 0<B) (hc : 2≤c) (hd : 2≤d)
    (hi : IndependentBases.Independent c d)
    (hcN : Nat.Coprime N c) (hdN : Nat.Coprime N d) (hdiv : ∀ell∈L,ell∣B)
    (hci : AdditionInjective c B {f:ℤ → K | Augmented N L B f})
    (hdi : AdditionInjective d B {f:ℤ → K | Augmented N L B f}) :
    ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → K,Augmented N L Q f → f=0 := by
  obtain ⟨m,hm,⟨E⟩⟩ := SpanningStationaryWords.exists_trace_family
    (by omega) (by omega) hB hcN hdN hdiv hci hdi
  obtain ⟨P,hP,F,hconc⟩ := SpanningClassicalConcentration.stationary_concentration
    (Nat.mul_pos hm hB) hc hd hi hcN hdN
    (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m) E
  apply concentration_forces_zero hN S hS hSL detector hP hdiv F
  intro ε hε T
  obtain ⟨Q,hQ,hMQ,hT,hnear⟩ := hconc ε hε T
  exact ⟨Q,hQ,(dvd_mul_left B m).trans hMQ,hT,hnear⟩

#print axioms two_injections_force_zero

open SpanningAdditionIntegerSystem SpanningIntegerRows SpanningActualKernel
  SpanningSlicedAddition GridAdmissibleGap

theorem two_rational_injections_force_zero {N B c d:ℕ} {L:Set ℕ}
    (hN:0<N) (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    (hSL : (S : Set ℕ) ⊆ L)
    (detector : ∀ (K : Type) [Field K], GridDifferenceDetector K N S)
    (hB:0<B) (hc:2≤c) (hd:2≤d)
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
    two_injections_force_zero hN S hS hSL (detector (ZMod p)) hB hc hd hi hcN hdN hdiv
      (hpc p hprime (by omega)) (hpd p hprime (by omega))
  exact ⟨Q,hQ,hBQ,augmented_zero_finite_field_rational hQ p hzero⟩


#print axioms two_rational_injections_force_zero

end QuantitativeArithmeticRetainedClosure
