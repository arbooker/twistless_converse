module

public import AsymptoticArithmeticNewCoefficientV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCompactObservationCount

open UpperHalfPlane MeasureTheory Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorComparison Asymptotics FinitenessOriginalInput

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The analytic summed-sector bound gives a reusable comparison with a total
dimension and its Euler lower bound. `AsymptoticEulerCountTheorem.admissible_level`
instantiates both inputs with the proved results for the actual classical
newspace, without using any sector dimension formula. -/
theorem count_littleO_of_total_newspace_inputs (hN : GridAdmissibleGap.Admissible N) (P : Parameters A)
    (K : CompactExhaustion ℍ) (dimension : ℕ → ℕ)
    (hlower : ∀ᶠ k in evenWeights,dimension k≤(S N k).ncard)
    (hdimension : (fun k => (dimension k:ℝ)-AsymptoticTotalNewCorner.arithmeticCoefficient N*(k:ℝ))
      =o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => ((S N k).ncard:ℝ)-(dimension k:ℝ))=o[evenWeights] (fun k => (k:ℝ)) := by
  apply count_littleO_of_incidence_bound_and_total_dimension A hN.1 P K
    (AsymptoticTotalNewCorner.arithmeticCoefficient N) dimension _ hlower hdimension
  let P' := AsymptoticReconstructedCount.parameters A P
  exact AsymptoticTotalNewCorner.totalTrace_le_arithmetic N hN P'.epsilon_pos (by omega : 1≤P'.s+4)

#print axioms count_littleO_of_total_newspace_inputs

end AsymptoticCompactObservationCount
