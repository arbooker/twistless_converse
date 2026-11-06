module

public import AsymptoticTotalCountReductionV1
public import AsymptoticClassicalNewDimensionTotalV1
public import AsymptoticClassicalNewEigenCountV1
public import FinitenessOriginalTheoremV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticEulerCountTheorem

open UpperHalfPlane Filter Asymptotics FinitenessOriginalInput
open AsymptoticSectorComparison AsymptoticClassicalCusp

/-- The asymptotic Euler count with an o_N(k) error, for the original complex
solution set at a fixed admissible level and through even weights. The proof
sums all sectors and compares only with the total classical newspace dimension. -/
theorem admissible_level (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => ((S N k).ncard : ℝ) -
      (Module.finrank ℂ (newSpace N hN.1 (k : ℤ)) : ℝ))
      =o[evenWeights] (fun k => (k : ℝ)) := by
  let : NeZero N := ⟨hN.1.ne'⟩
  obtain ⟨C, _, hfinite⟩ := FinitenessOriginalTheorem.even_weight N hN.1 hN.2.1 hN.2.2
  obtain ⟨Q, hQ, _, ⟨A⟩⟩ := FinitenessCertificate.exists_certificate N hN.1 hN.2.1 hN.2.2
  obtain ⟨P⟩ := FinitenessGlobalHeight.parameters_exist hN.1 hQ A
  apply AsymptoticCompactObservationCount.count_littleO_of_total_newspace_inputs A hN P
    (CompactExhaustion.choice ℍ)
    (fun k => Module.finrank ℂ (newSpace N hN.1 (k : ℤ)))
  · have he : ∀ᶠ k in evenWeights, Even k :=
      Filter.Eventually.filter_mono inf_le_right
        (Filter.eventually_principal.mpr (fun _ h => h))
    have hk : ∀ᶠ k in evenWeights, 0 < k :=
      (eventually_gt_atTop 0).filter_mono inf_le_left
    filter_upwards [hk, he] with k hk he
    exact newspace_dimension_le_euler_count N k hN.1 hk he (hfinite k hk he).1
  · exact AsymptoticClassicalDimension.new_dimension_littleO N hN

/-- Equivalent leading-coefficient formulation, with the local arithmetic
coefficient obtained from the total newspace. -/
theorem arithmetic_leading_term (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => ((S N k).ncard : ℝ) -
      AsymptoticTotalNewCorner.arithmeticCoefficient N * (k : ℝ))
      =o[evenWeights] (fun k => (k : ℝ)) := by
  have hh := (admissible_level N hN).add (AsymptoticClassicalDimension.new_dimension_littleO N hN)
  convert hh using 1
  ext k
  ring

#print axioms admissible_level
#print axioms arithmetic_leading_term
end AsymptoticEulerCountTheorem
