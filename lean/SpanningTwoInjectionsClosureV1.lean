module

public import SpanningConcentrationClosureV1
public import SpanningClassicalConcentrationV1
public import SpanningStationaryTraceV1

@[expose] public section

namespace SpanningTwoInjectionsClosure

open SpanningKernelDefects SpanningConcentrationClosure SpanningActualKernel
  GridAdmissibleGap SpanningSlicedAddition

variable {K : Type} [Field K] [Finite K]

/-- The complete stationary/automatic/grid argument over a finite field:
two independent coprime addition injections imply an actual zero augmented
kernel at some multiple of the base. -/
theorem two_injections_force_zero {N B c d : ℕ} {L : Set ℕ}
    (hN : Admissible N) (hB : 0<B) (hc : 2≤c) (hd : 2≤d)
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
  apply concentration_forces_zero hN hP hdiv F
  intro ε hε T
  obtain ⟨Q,hQ,hMQ,hT,hnear⟩ := hconc ε hε T
  exact ⟨Q,hQ,(dvd_mul_left B m).trans hMQ,hT,hnear⟩

#print axioms two_injections_force_zero

end SpanningTwoInjectionsClosure
