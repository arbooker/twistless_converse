module

public import QuantitativeMaassMetricPowerFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem metric_image_closed (L : H≃L[ℂ]H) (W : Submodule ℂ H)
    (hW : IsClosed (W:Set H)) : IsClosed (W.map L.toLinearMap:Set H) := by
  rw [Submodule.map_coe]
  exact L.isClosed_image.mpr hW

omit [CompleteSpace H] in
theorem metric_image_projection_factorization (L : H≃L[ℂ]H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    [(W.map L.toLinearMap).HasOrthogonalProjection] :
    (W.map L.toLinearMap).starProjection=
      (L.toContinuousLinearMap*W.starProjection)*
        (L.symm.toContinuousLinearMap*(W.map L.toLinearMap).starProjection) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y,hy,he⟩ := Submodule.mem_map.mp
    ((W.map L.toLinearMap).starProjection_apply_mem x)
  change L y=(W.map L.toLinearMap).starProjection x at he
  change (W.map L.toLinearMap).starProjection x=
    L (W.starProjection (L.symm ((W.map L.toLinearMap).starProjection x)))
  rw [←he,L.symm_apply_apply,Submodule.starProjection_eq_self_iff.mpr hy]

theorem metric_image_factor_norm (L : H≃L[ℂ]H)
    (W : Submodule ℂ H) [(W.map L.toLinearMap).HasOrthogonalProjection] :
    ‖L.symm.toContinuousLinearMap*(W.map L.toLinearMap).starProjection‖≤
      ‖L.symm.toContinuousLinearMap‖ := by
  apply (norm_mul_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (W.map L.toLinearMap).starProjection_norm_le (norm_nonneg L.symm.toContinuousLinearMap)

/-- Source transport for a genuine continuous linear change of metric.
The projection is the orthogonal projection onto the actual image space,
and all factorization and inverse-norm inputs are now discharged. -/
theorem metric_image_power_filter_error (L : H≃L[ℂ]H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    [(W.map L.toLinearMap).HasOrthogonalProjection]
    (F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1)
    {δ : ℝ} (hδ : ‖F*W.starProjection-W.starProjection‖≤δ) (m : ℕ) :
    ‖metricPowerFilter L.toContinuousLinearMap F m*(W.map L.toLinearMap).starProjection-
      (W.map L.toLinearMap).starProjection‖^2≤
      ‖L.symm.toContinuousLinearMap‖^2/
        (metricFilterScale L.toContinuousLinearMap*(((2*m:ℕ):ℝ)+1))+
      3*‖L.symm.toContinuousLinearMap‖^2*δ*‖L.toContinuousLinearMap‖^2 := by
  apply metricPowerFilter_source_error W.starProjection F
    (W.map L.toLinearMap).starProjection L.toContinuousLinearMap
    (L.symm.toContinuousLinearMap*(W.map L.toLinearMap).starProjection)
    (isSelfAdjoint_starProjection W) W.isIdempotentElem_starProjection
    W.starProjection_norm_le hF hF1
    (isSelfAdjoint_starProjection (W.map L.toLinearMap))
    (W.map L.toLinearMap).isIdempotentElem_starProjection
  · exact nonneg_iff_isPositive.mpr
      ⟨(W.map L.toLinearMap).starProjection_isSymmetric,
        (W.map L.toLinearMap).re_inner_starProjection_nonneg⟩
  · exact metric_image_projection_factorization L W
  · exact metric_image_factor_norm L W
  · exact hδ

#print axioms metric_image_closed
#print axioms metric_image_projection_factorization
#print axioms metric_image_factor_norm
#print axioms metric_image_power_filter_error
end QuantitativeMaass
