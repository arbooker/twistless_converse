module

public import QuantitativeArithmeticGeneralDimensionCoefficientV1
public import QuantitativeArithmeticRadicalFinitenessV1
public import AsymptoticClassicalNewEigenCountV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointRadicalBoundary

open Filter Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open FinitenessOriginalInput QuantitativeConcreteGoals

/-- The original Euler count exceeds the actual classical newspace
dimension throughout the proved radical finiteness range. -/
theorem holomorphicError_eventually_nonneg (N : ℕ) (hN : 0<N)
    (hrad : N<(∏ p∈N.primeFactors,p)^2) :
    ∀ᶠ k : ℕ in evenWeights,0≤holomorphicError N hN k := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨C,_,hfinite⟩ := QuantitativeArithmeticRadicalFiniteness.even_weight N hN hrad
  have he : ∀ᶠ k in evenWeights,Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hk : ∀ᶠ k in evenWeights,0<k := (eventually_gt_atTop 0).filter_mono inf_le_left
  filter_upwards [hk,he] with k hk he
  have hl := newspace_dimension_le_euler_count N k hN hk he (hfinite k hk he).1
  apply sub_nonneg.mpr
  exact_mod_cast hl

/-- The radical-range count can be compared with the actual arithmetic
incidence coefficient with only a bounded additive error. All finiteness
and classical dimension inputs are proved, with no admissibility restriction. -/
theorem literal_count_squeeze (N : ℕ) (hN : 0<N)
    (hrad : N<(∏ p∈N.primeFactors,p)^2) :
    ∃ C : ℝ,∀ᶠ k : ℕ in evenWeights,
      0≤holomorphicError N hN k ∧
      holomorphicError N hN k≤((S N k).ncard:ℝ)-
        AsymptoticTotalNewCorner.coefficient N hN*k+C := by
  obtain ⟨C,hC⟩ := QuantitativeArithmeticGeneralDimension.new_dimension_coefficient_bounded N hN
  refine ⟨C,?_⟩
  filter_upwards [hC,holomorphicError_eventually_nonneg N hN hrad] with k hk hlo
  refine ⟨hlo,?_⟩
  dsimp only [holomorphicError]
  have hd := (abs_le.mp hk).1
  linarith

/-- The two literal errors differ by O_N(1); this identity uses the
general positive-level dimension theorem, not a sectorwise dimension formula. -/
theorem count_errors_differ_isBigO_one (N : ℕ) (hN : 0<N) :
    (fun k : ℕ => holomorphicError N hN k-
      (((S N k).ncard:ℝ)-AsymptoticTotalNewCorner.coefficient N hN*k))
      =O[evenWeights] (fun _ : ℕ => (1:ℝ)) := by
  obtain ⟨C,hC⟩ := QuantitativeArithmeticGeneralDimension.new_dimension_coefficient_bounded N hN
  apply IsBigO.of_bound |C|
  filter_upwards [hC] with k hk
  have he : holomorphicError N hN k-
      (((S N k).ncard:ℝ)-AsymptoticTotalNewCorner.coefficient N hN*k)=
      -((Module.finrank ℂ (newSpace N hN (k:ℤ)):ℝ)-
        AsymptoticTotalNewCorner.coefficient N hN*k) := by
    dsimp only [holomorphicError]
    ring
  rw [he,Real.norm_eq_abs,abs_neg]
  simpa only [norm_one,mul_one] using hk.trans (le_abs_self C)

#print axioms holomorphicError_eventually_nonneg
#print axioms literal_count_squeeze
#print axioms count_errors_differ_isBigO_one

end QuantitativeEulerEndpointRadicalBoundary
