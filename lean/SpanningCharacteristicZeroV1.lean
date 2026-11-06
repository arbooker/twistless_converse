module

public import SpanningAdditionIntegerSystemV1
public import SpanningInitialSpectralVanishingV1

@[expose] public section

namespace SpanningCharacteristicZero

open SpanningFiniteEquations SpanningIntegerRows SpanningAdditionIntegerSystem
  SpanningActualKernel SpanningSlicedAddition SpanningInitialSpectralVanishing

theorem integer_equations_map {I J K K':Type*} [Fintype J] [CommRing K] [CommRing K']
    (φ:K →+* K') (E:I → J → ℤ) (v:J → K)
    (hv:Equations (fun i j => (E i j:K)) v) :
    Equations (fun i j => (E i j:K')) (fun j => φ (v j)) := by
  intro i
  have he := congrArg φ (hv i)
  simpa only [dotProduct,map_sum,map_mul,map_intCast,map_zero] using he

theorem integer_system_restrict_scalars {I J K K':Type*} [Fintype J] [Field K] [Field K']
    (φ:K →+* K') (E:I → J → ℤ)
    (hz:∀v:J → K',Equations (fun i j => (E i j:K')) v → v=0) :
    ∀v:J → K,Equations (fun i j => (E i j:K)) v → v=0 := by
  intro v hv
  have he := hz (fun j => φ (v j)) (integer_equations_map φ E v hv)
  funext j
  apply φ.injective
  simpa only [Pi.zero_apply,map_zero] using congrFun he j

theorem augmented_zero_restrict_scalars {N Q:ℕ} {L:Set ℕ} (hQ:0<Q)
    {K K':Type*} [Field K] [Field K'] (φ:K →+* K')
    (hz:∀f:ℤ → K',Augmented N L Q f → f=0) :
    ∀f:ℤ → K,Augmented N L Q f → f=0 := by
  apply (augmented_zero_iff hQ).mpr
  exact integer_system_restrict_scalars φ (augmentedRows N L hQ)
    ((augmented_zero_iff hQ).mp hz)

theorem addition_injective_restrict_scalars {N q B:ℕ} {L:Set ℕ}
    (hq:0<q) (hB:0<B) {K K':Type*} [Field K] [Field K'] (φ:K →+* K')
    (hi:AdditionInjective q B {f:ℤ → K' | Augmented N L B f}) :
    AdditionInjective q B {f:ℤ → K | Augmented N L B f} := by
  apply (addition_injective_iff hq hB).mpr
  exact integer_system_restrict_scalars φ (additionRows N L hq hB)
    ((addition_injective_iff hq hB).mp hi)

theorem rational_augmented_zero_of_spectral_count {N Q:ℕ} {S:Set ℕ}
    (hQ:0<Q) (hdiv:∀q∈S,q∣Q)
    (hsize:((remainingFrequencies Q S).card:ℝ)<radius N Q 1) :
    ∀f:ℤ → ℚ,Augmented N S Q f → f=0 :=
  augmented_zero_restrict_scalars hQ (algebraMap ℚ ℂ)
    (complex_augmented_zero_of_spectral_count hQ hdiv hsize)

#print axioms integer_system_restrict_scalars
#print axioms rational_augmented_zero_of_spectral_count

end SpanningCharacteristicZero
