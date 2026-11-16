module

public import SpanningFiniteEquationsV1
public import SpanningIntegerRowsV1

@[expose] public section

namespace SpanningCriterionScalarExtension

open SpanningFiniteEquations SpanningIntegerCertificates SpanningIntegerRows
  SpanningActualKernel

/-- A rational integer-row system with zero kernel has zero kernel over
any characteristic-zero field. The proof transports a finite integer certificate. -/
theorem integer_system_extend {I J K : Type*} [Fintype J] [Field K] [CharZero K]
    (E : I → J → ℤ)
    (hz : ∀ v : J → ℚ, Equations (fun i j => (E i j : ℚ)) v → v = 0) :
    ∀ v : J → K, Equations (fun i j => (E i j : K)) v → v = 0 := by
  classical
  obtain ⟨s,hs⟩ := finite_equations (fun i j => (E i j : ℚ)) hz
  let A : Matrix s J ℤ := fun i j => E i.val j
  have hA : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec :=
    submatrix_injective (fun i j => (E i j : ℚ)) s hs
  obtain ⟨D,hD,C,hC⟩ := rational_injective_certificate A hA
  have hi := integer_certificate_injective (K:=K) A C (D : ℤ) hC
    (by exact_mod_cast hD.ne')
  intro v hv
  apply hi
  ext i
  change (∑ j, (E i.val j : K) * v j) = _
  simpa only [dotProduct, Matrix.mulVec_zero, Pi.zero_apply] using hv i.val

theorem augmented_zero_extend {N Q : ℕ} {L : Set ℕ} (hQ : 0 < Q)
    {K : Type*} [Field K] [CharZero K]
    (hz : ∀ f : ℤ → ℚ, Augmented N L Q f → f = 0) :
    ∀ f : ℤ → K, Augmented N L Q f → f = 0 := by
  apply (augmented_zero_iff hQ).mpr
  exact integer_system_extend (augmentedRows N L hQ)
    ((augmented_zero_iff hQ).mp hz)

#print axioms augmented_zero_extend

end SpanningCriterionScalarExtension
