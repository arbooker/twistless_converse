module

public import QuantitativeEulerOldProjectionClassicalDimensionTotalV1
public import AsymptoticClassicalNewEigenCountV1
public import FinitenessOriginalTheoremV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionClassicalDimension

open Filter Asymptotics AsymptoticSectorComparison AsymptoticClassicalCusp
open FinitenessOriginalInput QuantitativeConcreteGoals

/-- The literal Euler count exceeds the total classical newspace dimension.
Finiteness, the normalized eigenform family, and every Euler relation are
provided by the established concrete theorems, not supplied as premises. -/
theorem holomorphicError_eventually_nonneg (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∀ᶠ k : ℕ in evenWeights, 0 ≤ holomorphicError N hN.1 k := by
  let : NeZero N := ⟨hN.1.ne'⟩
  obtain ⟨C, _, hfinite⟩ := FinitenessOriginalTheorem.even_weight N hN.1 hN.2.1 hN.2.2
  have he : ∀ᶠ k in evenWeights, Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  have hk : ∀ᶠ k in evenWeights, 0 < k := (eventually_gt_atTop 0).filter_mono inf_le_left
  filter_upwards [hk, he] with k hk he
  have hl := newspace_dimension_le_euler_count N k hN.1 hk he (hfinite k hk he).1
  apply sub_nonneg.mpr
  exact_mod_cast hl

/-- Quantitative count boundary: the literal nonnegative excess over the
classical newspace is bounded by the excess over the arithmetic main term
plus a fixed level-dependent constant. A regular-trace upper bound can
therefore be inserted directly; no physical simple-prime gap or individual
classical sign-sector dimension formula is required. -/
theorem literal_count_squeeze (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in evenWeights,
      0 ≤ holomorphicError N hN.1 k ∧
      holomorphicError N hN.1 k ≤
        ((S N k).ncard : ℝ) - AsymptoticTotalNewCorner.arithmeticCoefficient N * k + C := by
  obtain ⟨C, hC⟩ := new_dimension_bounded N hN
  refine ⟨C, ?_⟩
  filter_upwards [hC, holomorphicError_eventually_nonneg N hN] with k hk hlo
  refine ⟨hlo, ?_⟩
  dsimp only [holomorphicError]
  have hd := (abs_le.mp hk).1
  linarith

/-- The two literal counting errors differ by a bounded function of the
weight. This records the exact quantitative upgrade from the old little-o
classical-dimension interface. -/
theorem count_errors_differ_isBigO_one (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (fun k : ℕ => holomorphicError N hN.1 k -
      (((S N k).ncard : ℝ) - AsymptoticTotalNewCorner.arithmeticCoefficient N * k))
      =O[evenWeights] (fun _ : ℕ => (1 : ℝ)) := by
  have hh := (new_dimension_isBigO_one N hN).neg_left
  convert hh using 1
  funext k
  dsimp only [holomorphicError]
  ring

#print axioms holomorphicError_eventually_nonneg
#print axioms literal_count_squeeze
#print axioms count_errors_differ_isBigO_one
end QuantitativeEulerOldProjectionClassicalDimension
