module

public import SpanningCriterionRetainedGridV1
public import QuantitativeArithmeticRetainedBoundedAxisV1
public import QuantitativeArithmeticRetainedTraceRemovalV1
public import QuantitativeArithmeticRetainedCertificateV1

@[expose] public section

namespace SpanningCriterion

open SpanningActualKernel QuantitativeArithmeticRetainedCertificate

/-- Sufficiency of the exact arithmetic criterion, for every positive level.
The retained set may be empty and its primes may divide the level. -/
theorem zero_kernel {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcond : Condition N P) :
    ∃ Q : ℕ, 0 < Q ∧ N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) Q f → f = 0 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  exact QuantitativeArithmeticRetainedTraceRemoval.retained_zero_of_bounded_axis hN P hpos
    (QuantitativeArithmeticRetainedBoundedAxis.bounded_axis hN P hpos
      (SpanningCriterionRetainedGrid.grid_difference_detector hN P hP hcond))

/-- The row-span form of the general augmented spanning theorem. -/
theorem spanning {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcond : Condition N P) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      Submodule.span ℚ (Set.range (fun i j => (rows N P hQ i j : ℚ))) = ⊤ := by
  obtain ⟨Q,hQ,hNQ,hPQ,hzero⟩ := zero_kernel hN P hP hcond
  exact ⟨Q,hQ,hNQ,hPQ,(span_top_iff hN hQ P).mpr hzero⟩

/-- Unconditional existence of finite rational reconstruction certificates
for the augmented system, for all positive levels. -/
theorem exists_certificate {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcond : Condition N P) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      Nonempty (Certificate N P Q hQ) := by
  obtain ⟨Q,hQ,hNQ,hPQ,hzero⟩ := zero_kernel hN P hP hcond
  exact ⟨Q,hQ,hNQ,hPQ,exists_certificate_of_zero hN hQ P hzero⟩

/-- Literal vanishing: a positive length divisible by every retained prime,
with the legal primitive rows and unrestricted retained complete rows spanning. -/
def Vanishing (N : ℕ) (P : Finset ℕ) : Prop :=
  ∃ Q : ℕ, ∃ hQ : 0 < Q, (∀ p ∈ P, p ∣ Q) ∧
    Submodule.span ℚ (Set.range (fun i j => (rows N P hQ i j : ℚ))) = ⊤

theorem vanishing_iff_zero {N : ℕ} (hN : 0 < N) (P : Finset ℕ) :
    Vanishing N P ↔ ∃ Q : ℕ, 0 < Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) Q f → f = 0 := by
  constructor
  · rintro ⟨Q,hQ,hPQ,htop⟩
    exact ⟨Q,hQ,hPQ,(span_top_iff hN hQ P).mp htop⟩
  · rintro ⟨Q,hQ,hPQ,hzero⟩
    exact ⟨Q,hQ,hPQ,(span_top_iff hN hQ P).mpr hzero⟩

theorem vanishing_of_condition {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcond : Condition N P) : Vanishing N P := by
  obtain ⟨Q,hQ,_hNQ,hPQ,htop⟩ := spanning hN P hP hcond
  exact ⟨Q,hQ,hPQ,htop⟩

#print axioms vanishing_of_condition
#print axioms exists_certificate

end SpanningCriterion
