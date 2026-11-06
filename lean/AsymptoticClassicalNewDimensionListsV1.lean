module

public import AsymptoticClassicalNewDimensionInductionV1
public import AsymptoticClassicalNewDimensionBasesV1
public import AsymptoticClassicalNewDimensionAdmissibleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open scoped Topology

/-- A partial newspace imposing every prime condition is the genuine newspace. -/
theorem partialNewSpace_eq_new_of_covers (N : ℕ) (hN : 0 < N) (k : ℤ) (S : Set ℕ)
    (hS : ∀ p, p.Prime → p ∣ N → p ∈ S) :
    partialNewSpace N hN k S = newSpace N hN k := by
  ext f
  rw [mem_partialNewSpace, mem_newSpace]
  constructor
  · intro hf p
    exact hf p (hS p.val p.property.1 p.property.2)
  · exact fun hf p _ => hf p

/-- Actual total newspace dimension for an admissible level without repeated
 prime factors, with its finite-difference coefficient. -/
theorem new_dimension_all_list (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h4 : ¬4 ∣ N) :
    (fun k : ℕ => (Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
      simpleDifference (allPrimeList N) fullLeading N * k)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  have hh := partial_dimension_difference 1 ∅ fullLeading
    (fun M hM _ => empty_dimension_littleO M hM) (allPrimeList N) N hN.1 (one_dvd N)
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
theorem new_dimension_odd_list (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h4 : 4 ∣ N) :
    (fun k : ℕ => (Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
      simpleDifference (oddPrimeList N) twoLeading N * k)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  have hh := partial_dimension_difference 4 {2} twoLeading
    (fun M hM h4M => two_dimension_littleO M hM h4M) (oddPrimeList N) N hN.1 h4
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

#print axioms partialNewSpace_eq_new_of_covers
#print axioms new_dimension_all_list
#print axioms new_dimension_odd_list

end AsymptoticClassicalDimension
