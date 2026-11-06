module

public import AsymptoticCylinderTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderTerminal

open MeasureTheory Set ContinuousLinearMap Filter

/-- Nested height restrictions compose to the higher restriction. -/
theorem projection_comp_of_le {Y ε : ℝ} (hY : Y≤ε) :
    (projection ε).comp (projection Y)=projection ε := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [projection_coeFn ε (projection Y f),projection_coeFn Y f,
    projection_coeFn ε f] with z he hy hf
  classical
  rw [comp_apply,he,hf]
  by_cases hz : z∈region ε
  · have hzy : z∈region Y := hY.trans hz
    rw [indicator_of_mem hz,indicator_of_mem hz,hy,indicator_of_mem hzy]
  · rw [indicator_of_notMem hz,indicator_of_notMem hz]

/-- Height restriction commutes with the capped-weight inclusion. -/
theorem projection_comp_inclusion {ε : ℝ} (hε : 0<ε) (Y : ℝ) :
    (projection Y).comp (AsymptoticCylinder.inclusion hε)=
      (AsymptoticCylinder.inclusion hε).comp (projection Y) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [projection_coeFn Y (AsymptoticCylinder.inclusion hε f),
    AsymptoticCylinder.inclusion_coeFn hε f,
    AsymptoticCylinder.inclusion_coeFn hε (projection Y f),projection_coeFn Y f] with z hp hi hip hpf
  change projection Y (AsymptoticCylinder.inclusion hε f) z=
    AsymptoticCylinder.inclusion hε (projection Y f) z
  rw [hp,hip,hpf]
  classical
  by_cases hz : z∈region Y
  · rw [indicator_of_mem hz,indicator_of_mem hz,hi]
  · rw [indicator_of_notMem hz,indicator_of_notMem hz,mul_zero]

/-- The norm estimate uses the extra capped weight in the actual
cylinder realization, so it is independent of the holomorphic weight. -/
theorem inclusion_cut_error {ε Y : ℝ} (hε : 0<ε) (hY : 0≤Y) :
    ‖AsymptoticCylinder.inclusion hε-(projection Y).comp (AsymptoticCylinder.inclusion hε)‖≤Y/ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hY hε.le)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (AsymptoticCylinder.inclusion hε f)
      (projection Y (AsymptoticCylinder.inclusion hε f)),
    projection_coeFn Y (AsymptoticCylinder.inclusion hε f),
    AsymptoticCylinder.inclusion_coeFn hε f,AsymptoticCylinder.height_positive] with z hd hp hi hz
  change ‖(AsymptoticCylinder.inclusion hε f-projection Y (AsymptoticCylinder.inclusion hε f)) z‖≤_
  rw [hd,Pi.sub_apply,hp]
  classical
  by_cases hy : z∈region Y
  · rw [indicator_of_mem hy,sub_self,norm_zero]
    exact mul_nonneg (div_nonneg hY hε.le) (norm_nonneg _)
  · rw [indicator_of_notMem hy,sub_zero,hi,norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hy' : z.2≤Y := le_of_not_ge hy
    have hw : 0≤min (z.2/ε) 1 := le_min (div_nonneg hz.le hε.le) zero_le_one
    rw [AsymptoticCylinder.weight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
    exact (min_le_left _ _).trans (div_le_div_of_nonneg_right hy' hε.le)

#print axioms projection_comp_of_le
#print axioms projection_comp_inclusion
#print axioms inclusion_cut_error

end AsymptoticCylinderTerminal
