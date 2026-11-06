module

public import QuantitativeArithmeticRetainedGridV1
public import QuantitativeArithmeticRetainedBoundedAxisV1
public import QuantitativeArithmeticRetainedTraceRemovalV1
public import QuantitativeArithmeticRetainedCertificateV1

@[expose] public section

namespace QuantitativeArithmeticAugmentedSpanning

open SpanningActualKernel QuantitativeArithmeticRetainedCertificate

/-- Augmented spanning for every positive level. The only extra rows are
complete rows at a finite set of primes whose product exceeds `sqrt N`.
The retained primes may divide the level. -/
theorem zero_kernel {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2) :
    ∃ Q : ℕ, 0 < Q ∧ N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) Q f → f = 0 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  exact QuantitativeArithmeticRetainedTraceRemoval.retained_zero_of_bounded_axis hN P hpos
    (QuantitativeArithmeticRetainedBoundedAxis.bounded_axis hN P hpos
      (QuantitativeArithmeticRetainedGrid.grid_difference_detector hN P hP hlarge))

/-- The row-span form of the general augmented spanning theorem. -/
theorem spanning {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      Submodule.span ℚ (Set.range (fun i j => (rows N P hQ i j : ℚ))) = ⊤ := by
  obtain ⟨Q,hQ,hNQ,hPQ,hzero⟩ := zero_kernel hN P hP hlarge
  exact ⟨Q,hQ,hNQ,hPQ,(span_top_iff hN hQ P).mpr hzero⟩

/-- Unconditional existence of finite rational reconstruction certificates
for the augmented system, for all positive levels. -/
theorem exists_certificate {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      Nonempty (Certificate N P Q hQ) := by
  obtain ⟨Q,hQ,hNQ,hPQ,hzero⟩ := zero_kernel hN P hP hlarge
  exact ⟨Q,hQ,hNQ,hPQ,exists_certificate_of_zero hN hQ P hzero⟩

/-- In the radical range, no good auxiliary prime is needed: the primes
already dividing the level provide all retained complete rows. -/
theorem radical_certificate {N : ℕ} (hN : 0 < N)
    (hrad : N < (∏ p ∈ N.primeFactors, p)^2) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧
      Nonempty (Certificate N N.primeFactors Q hQ) := by
  obtain ⟨Q,hQ,hNQ,_hPQ,hcert⟩ := exists_certificate hN N.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) hrad
  exact ⟨Q,hQ,hNQ,hcert⟩

/-- The same corollary with the paper's real square-root inequality. -/
theorem radical_certificate_sqrt {N : ℕ} (hN : 0 < N)
    (hrad : Real.sqrt (N : ℝ) < ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ)) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧
      Nonempty (Certificate N N.primeFactors Q hQ) := by
  apply radical_certificate hN
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N)
  have hnonneg := Real.sqrt_nonneg (N : ℝ)
  have hreal : (N : ℝ) < (((∏ p ∈ N.primeFactors, p : ℕ) : ℝ))^2 := by nlinarith
  exact_mod_cast hreal

#print axioms zero_kernel
#print axioms spanning
#print axioms exists_certificate
#print axioms radical_certificate_sqrt

end QuantitativeArithmeticAugmentedSpanning
