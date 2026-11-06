module

public import AsymptoticClassicalNewDimensionListsV1
public import AsymptoticClassicalNewDimensionCoefficientV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open scoped Topology

/-- The actual total classical newspace has the required arithmetic leading
 coefficient and an o_N(k) error along even weights. This uses full cusp
 dimensions and old-image recurrences, with no sector dimension formula. -/
theorem new_dimension_littleO (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => (Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ) -
      AsymptoticTotalNewCorner.arithmeticCoefficient N * k)
      =o[evenWeights] (fun k => (k : ℝ)) := by
  by_cases h4 : 4 ∣ N
  · have hh := new_dimension_odd_list N hN h4
    have hc := twoDifference_arithmetic N hN.1 h4 (oddPrimeList_simple N hN)
    change simpleDifference (oddPrimeList N) twoLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    simpa only [hc] using hh
  · have hh := new_dimension_all_list N hN h4
    have hc := fullDifference_arithmetic N hN.1 (allPrimeList_simple N hN h4)
    change simpleDifference (allPrimeList N) fullLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    simpa only [hc] using hh

#print axioms new_dimension_littleO

end AsymptoticClassicalDimension
