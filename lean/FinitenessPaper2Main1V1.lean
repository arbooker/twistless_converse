module

public import FinitenessAllLevelBoundedFinitenessV1
public import FinitenessPaper2GrowthV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessPaper2

open Complex Set Filter Asymptotics

/-- `paper2-Astra.tex`, Theorem `thm:main1`, at EVERY positive level and
positive even weight, for every real exponent. The Big-O constant remains
individual to each sequence. No admissible-level or geometric premise is
assumed. -/
theorem main1 (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (heven : Even k) (σ : ℝ) :
    (E N k σ).Finite := by
  obtain ⟨p, hp, hgood, hlarge⟩ := exists_large_good_prime N hN
  apply (FinitenessAllLevelBoundedFiniteness.bounded_original_even
    hN hp hgood hlarge hk heven ((p : ℝ) ^ σ + (p : ℝ) ^ (-σ))).subset
  intro f hf
  exact ⟨((mem_iff_original N k σ f).mp hf).1, (good_prime_bound hf hp hgood).2⟩

/-- The same full theorem stated with the literal original Euler product,
entire finite-order continuation, functional equation and bad-prime input.
The quantification of the implicit Big-O constant is unchanged. -/
theorem main1_original (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (heven : Even k) (σ : ℝ) :
    {f : ℕ → ℂ | FinitenessOriginalInput.IsSolution N k f ∧
      f =O[atTop] (fun n : ℕ => (n : ℝ) ^ σ)}.Finite := by
  convert main1 N k hN hk heven σ using 1
  ext f
  exact (mem_iff_original N k σ f).symm

/-- The stronger intermediate proposition: bounding one good retained
prime coefficient suffices at every positive level and positive even weight. -/
theorem bounded_eigenvalue_finiteness {N k p : ℕ}
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (B : ℝ) :
    {f : ℕ → ℂ | FinitenessOriginalInput.IsSolution N k f ∧ ‖f p‖ ≤ B}.Finite :=
  FinitenessAllLevelBoundedFiniteness.bounded_original_even hN hp hgood hlarge hk heven B

#print axioms main1
#print axioms main1_original
#print axioms bounded_eigenvalue_finiteness

end FinitenessPaper2
