module

public import QuantitativeEulerOldProjectionClassicalDimensionInductionV1
public import AsymptoticClassicalNewDimensionCoefficientV1
public import AsymptoticClassicalNewDimensionListsV1
public import AsymptoticClassicalNewDimensionBasesV1
public import AsymptoticClassicalNewDimensionAdmissibleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open AsymptoticClassicalDimension
open scoped Topology

/-- Actual total newspace dimension for an admissible level without repeated
 prime factors, with its finite-difference coefficient. -/
theorem new_dimension_all_list_bounded (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h4 : ¬4 ∣ N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
        simpleDifference (allPrimeList N) fullLeading N * k| ≤ C := by
  have hh := partial_dimension_bounded_difference 1 ∅ fullLeading
    (fun M hM _ => empty_dimension_bounded M hM) (allPrimeList N) N hN.1 (one_dvd N)
    (allPrimeList_simple N hN h4) (fun _ _ => Nat.coprime_one_right _) (by simp)
  have hs (k : ℕ) : partialNewSpace N hN.1 (k : ℤ)
      (((allPrimeList N).toFinset : Set ℕ) ∪ ∅) = newSpace N hN.1 (k : ℤ) := by
    apply partialNewSpace_eq_new_of_covers
    intro p hp hd
    exact Or.inl (List.mem_toFinset.mpr (allPrimeList_covers N hN.1 p hp hd))
  have hd (k : ℕ) := congrArg
    (fun U : Submodule ℂ (CuspForm (level N) (k : ℤ)) => Module.finrank ℂ U) (hs k)
  simpa only [hd] using hh

/-- Actual total newspace dimension when the 2-part is repeated: its condition
 is imposed first, and the remaining induction uses only simple odd primes. -/
theorem new_dimension_odd_list_bounded (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h4 : 4 ∣ N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
        simpleDifference (oddPrimeList N) twoLeading N * k| ≤ C := by
  have hh := partial_dimension_bounded_difference 4 {2} twoLeading
    (fun M hM h4M => two_dimension_bounded M hM h4M) (oddPrimeList N) N hN.1 h4
    (oddPrimeList_simple N hN) (oddPrimeList_coprime_four N)
    (fun p hp => by simpa only [Set.mem_singleton_iff] using oddPrimeList_ne_two N p hp)
  have hs (k : ℕ) : partialNewSpace N hN.1 (k : ℤ)
      (((oddPrimeList N).toFinset : Set ℕ) ∪ {2}) = newSpace N hN.1 (k : ℤ) := by
    apply partialNewSpace_eq_new_of_covers
    intro p hp hd
    rcases oddPrimeList_covers N hN.1 p hp hd with hs | hs
    · exact Or.inl (List.mem_toFinset.mpr hs)
    · exact Or.inr (Set.mem_singleton_iff.mpr hs)
  have hd (k : ℕ) := congrArg
    (fun U : Submodule ℂ (CuspForm (level N) (k : ℤ)) => Module.finrank ℂ U) (hs k)
  simpa only [hd] using hh

/-- The actual total newspace has its arithmetic leading coefficient
with an O_N(1) remainder along even weights. No sector dimension formula
or physical simple-prime spectral gap is used. -/
theorem new_dimension_bounded (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
        AsymptoticTotalNewCorner.arithmeticCoefficient N * k| ≤ C := by
  by_cases h4 : 4 ∣ N
  · have hh := new_dimension_odd_list_bounded N hN h4
    have hc := twoDifference_arithmetic N hN.1 h4 (oddPrimeList_simple N hN)
    change simpleDifference (oddPrimeList N) twoLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    simpa only [hc] using hh
  · have hh := new_dimension_all_list_bounded N hN h4
    have hc := fullDifference_arithmetic N hN.1 (allPrimeList_simple N hN h4)
    change simpleDifference (allPrimeList N) fullLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    simpa only [hc] using hh

theorem new_dimension_isBigO_one (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => (Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
      AsymptoticTotalNewCorner.arithmeticCoefficient N * k)
      =O[evenWeights] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := new_dimension_bounded N hN
  apply Asymptotics.IsBigO.of_bound C
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hC

#print axioms new_dimension_bounded
#print axioms new_dimension_isBigO_one
end QuantitativeEulerOldProjectionClassicalDimension
