module

public import QuantitativeMaassWeightedCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Weighted

/-- A pointwise logarithmic-gradient bound transfers to the pair of actual
L2 cutoff-gradient multipliers, without losing a dimension-dependent factor. -/
theorem gradient_pair_bound (N : ℕ) (b : Cutoff N) (a : ℝ)
    (ha : ∀ z : ℍ, ‖cutoffGradient true b.value z‖^2+‖cutoffGradient false b.value z‖^2≤
      a^2*‖upperFunction b.value z‖^2)
    (f : Lp ℂ 2 (quotientMeasure N)) :
    ‖gradientMultiplier N b true f‖^2+‖gradientMultiplier N b false f‖^2≤
      a^2*‖multiplier N b f‖^2 := by
  let dx := gradientMultiplier N b true f
  let dy := gradientMultiplier N b false f
  let w := multiplier N b f
  have hx := (Lp.memLp dx).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hy := (Lp.memLp dy).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hw := (Lp.memLp w).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  change ‖dx‖^2+‖dy‖^2≤a^2*‖w‖^2
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral dx,AsymptoticL2Multiplier.norm_sq_eq_integral dy,
    AsymptoticL2Multiplier.norm_sq_eq_integral w,← integral_add hx hy,← integral_const_mul]
  apply integral_mono_ae (hx.add hy) (hw.const_mul (a^2))
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn (cutoffGradient true b.value)
      (cutoffGradient_continuous true b.value b.smooth).aestronglyMeasurable
      (Eventually.of_forall (cutoffGradient_norm_le true b.value b.gradient_bound)) f,
    AsymptoticL2Multiplier.operator_coeFn (cutoffGradient false b.value)
      (cutoffGradient_continuous false b.value b.smooth).aestronglyMeasurable
      (Eventually.of_forall (cutoffGradient_norm_le false b.value b.gradient_bound)) f,
    AsymptoticL2Multiplier.operator_coeFn (upperFunction b.value)
      (upperFunction_continuous b.smooth).aestronglyMeasurable
      (Eventually.of_forall b.value_bound) f] with z hxz hyz hwz
  change ‖dx z‖^2+‖dy z‖^2≤a^2*‖w z‖^2
  change dx z=cutoffGradient true b.value z*f z at hxz
  change dy z=cutoffGradient false b.value z*f z at hyz
  change w z=upperFunction b.value z*f z at hwz
  rw [hxz,hyz,hwz,norm_mul,norm_mul,norm_mul,mul_pow,mul_pow,mul_pow]
  have h := mul_le_mul_of_nonneg_right (ha z) (sq_nonneg ‖f z‖)
  nlinarith

#print axioms gradient_pair_bound

end QuantitativeMaass.Weighted
