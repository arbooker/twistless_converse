module

public import AsymptoticClassicalNewPrimeEigenbasisV1
public import AsymptoticClassicalNewEigenSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane AsymptoticClassicalLSeries FinitenessOriginalInput

/-- The actual total newspace supplies `finrank` distinct complex Euler
solutions, without resolving any Fricke-sign sector dimension. -/
theorem exists_newspace_euler_family (N k : ℕ) [NeZero N] (hN : 0 < N)
    (hk : 0 < k) (heven : Even k) :
    ∃ a : Fin (Module.finrank ℂ (newSpace N hN (k : ℤ))) → (ℕ → ℂ),
      Function.Injective a ∧ ∀ j, IsSolution N k (a j) := by
  obtain ⟨f, hf, hone, he⟩ := exists_normalized_new_prime_family N hN (k : ℤ)
  refine ⟨fun j => coefficients (f j).val, ?_, ?_⟩
  · intro i j hij
    exact hf (Subtype.ext (coefficients_injective hij))
  · intro j
    obtain ⟨e, he⟩ := he j
    exact new_prime_eigen_isSolution N k hN hk heven (f j).val (f j).property (hone j) e he

/-- The lower Euler count uses the total newspace dimension alone.
Finiteness of the Euler set is supplied by the proved finiteness theorem. -/
theorem newspace_dimension_le_euler_count (N k : ℕ) [NeZero N] (hN : 0 < N)
    (hk : 0 < k) (heven : Even k) (hS : (S N k).Finite) :
    Module.finrank ℂ (newSpace N hN (k : ℤ)) ≤ (S N k).ncard := by
  obtain ⟨a, ha, hmem⟩ := exists_newspace_euler_family N k hN hk heven
  have hsub : Set.range a ⊆ S N k := by
    rintro _ ⟨j, rfl⟩
    exact hmem j
  have hc := Set.ncard_le_ncard hsub hS
  rw [Set.ncard_range_of_injective ha] at hc
  simpa using hc

#print axioms exists_newspace_euler_family
#print axioms newspace_dimension_le_euler_count
end AsymptoticClassicalCusp
