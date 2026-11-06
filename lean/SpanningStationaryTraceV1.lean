module

public import SpanningCoherentLiftsV1

@[expose] public section

namespace SpanningStationaryWords

open SpanningActualKernel SpanningSlicedAddition SpanningLinearKernels
open SpanningFiniteDimensions SpanningTowerTraces SpanningCoherentLifts
variable {K : Type} [Field K]

theorem exists_trace_family {N B c d : ℕ} {L : Set ℕ}
    (hc : 0<c) (hd : 0<d) (hB : 0<B) (hcN : Nat.Coprime N c) (hdN : Nat.Coprime N d)
    (hdiv : ∀ell∈L,ell∣B)
    (hci : AdditionInjective c B {v:ℤ → K | Augmented N L B v})
    (hdi : AdditionInjective d B {v:ℤ → K | Augmented N L B v}) :
    ∃m:ℕ,∃_hm:0<m,Nonempty (∀a b:ℕ,TraceLift (K:=K) N L (m*B) (c^a*d^b)) := by
  obtain ⟨a₀,b₀,hstat⟩ := stationary_dimensions hc hd hB hcN hdN hdiv hci hdi
  let m := c^a₀*d^b₀
  have hm : 0<m := Nat.mul_pos (pow_pos hc _) (pow_pos hd _)
  refine ⟨m,hm,⟨fun a b => ?_⟩⟩
  apply TraceLift.ofStationary (Nat.mul_pos (pow_pos hc _) (pow_pos hd _)) hm hB
    ((hcN.pow_right a).mul_right (hdN.pow_right b)) hdiv
    (uniform_two_powers hc hd hcN hdN hdiv hci hdi a b)
  simpa [m,pow_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hstat a b

#print axioms exists_trace_family

end SpanningStationaryWords
