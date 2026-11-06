module

public import FinitenessPaper2CoefficientCompactnessV1
public import AsymptoticClassicalEulerProductV1

set_option autoImplicit false

public section

namespace FinitenessPaper2

open Filter Asymptotics Set
open scoped Topology

theorem closure_exponent_nonneg {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ closure (E N k σ)) : 0 ≤ σ := by
  by_contra! hσ
  simp only [negative_exponent_empty hN hσ, closure_empty, notMem_empty] at hf

/-- The literal infinite Euler product is recovered at coefficient limits
from the closed recurrences and polynomial envelope. It is not simply
assumed to be a closed predicate. -/
theorem closure_eulerProduct {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ closure (E N k σ)) :
    FinitenessOriginalInput.EulerProduct N f := by
  apply AsymptoticClassicalEulerProduct.eulerProduct_of_arithmetic
    (closure_zero hf) (closure_one hf) (closure_growth hN hf)
    (fun _ _ hc => closure_multiplicative hf hc)
  intro p hp j
  exact closure_recurrence hf hp j

/-- Every coefficient limit satisfies all original Euler-data fields.
Entire finite-order continuation and its functional equation are deliberately
not claimed here; those require the Fourier/Mellin limit bridge. -/
theorem closure_eulerData {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ closure (E N k σ)) :
    FinitenessOriginalInput.EulerData N f where
  zero := closure_zero hf
  growth := ⟨σ+1, by linarith [closure_exponent_nonneg hN hf], closure_growth hN hf⟩
  euler := closure_eulerProduct hN hf
  bad := closure_bad_primes hf

/-- Actual Euler solutions with a fixed exponent have coefficientwise
convergent subsequences whose limits retain the original Euler data. -/
theorem exists_eulerData_subsequence {N k : ℕ} {σ : ℝ}
    (hN : 0 < N) (a : ℕ → (ℕ → ℂ)) (ha : ∀ j, a j ∈ E N k σ) :
    ∃ f : ℕ → ℂ, FinitenessOriginalInput.EulerData N f ∧ f 1 = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ n : ℕ, Tendsto (fun j => a (φ j) n) atTop (𝓝 (f n)) := by
  obtain ⟨f, hf, φ, hφ, ht⟩ := (coefficient_closure_isCompact hN).tendsto_subseq
    (fun j => subset_closure (ha j))
  refine ⟨f, closure_eulerData hN hf, closure_one hf, φ, hφ, ?_⟩
  intro n
  exact ((continuous_apply n).tendsto f).comp ht

#print axioms closure_eulerProduct
#print axioms closure_eulerData
#print axioms exists_eulerData_subsequence

end FinitenessPaper2
