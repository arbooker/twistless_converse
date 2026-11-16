module

public import QuantitativeMaassMetricImageFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scale is explicit so one finite polynomial can be used in both
physical and regular representations with a common norm bound. -/
def scaledMetricPowerFilter (γ : ℝ) (J F : H→L[ℂ]H) (m : ℕ) : H→L[ℂ]H :=
  1-(1-γ • (J*F*J.adjoint))^m

theorem scaled_metric_contraction (J F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1)
    {γ : ℝ} (hγ : 0≤γ) (hscale : γ*‖J‖^2≤1) :
    0≤γ • (J*F*J.adjoint) ∧ γ • (J*F*J.adjoint)≤1 := by
  have hp : 0≤J*F*J.adjoint := by
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj J.adjoint
    simpa only [adjoint_adjoint,←mul_def,mul_assoc] using nonneg_iff_isPositive.mpr hh
  have hc := star_left_conjugate_le_conjugate hF1 J.adjoint
  change J.adjoint.adjoint*F*J.adjoint≤J.adjoint.adjoint*1*J.adjoint at hc
  rw [adjoint_adjoint,mul_one] at hc
  have hb := smul_le_smul_of_nonneg_left (hc.trans (cogram_le_norm_square J)) hγ
  have hlast : (γ*‖J‖^2) • (1:H→L[ℂ]H)≤1 := by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right hscale
      (zero_le_one : (0:H→L[ℂ]H)≤1)
  have hb' : γ • (J*F*J.adjoint)≤(γ*‖J‖^2) • (1:H→L[ℂ]H) := by
    simpa only [smul_smul] using hb
  exact ⟨smul_nonneg hγ hp,hb'.trans hlast⟩

theorem scaledMetricPowerFilter_order (J F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1)
    {γ : ℝ} (hγ : 0≤γ) (hscale : γ*‖J‖^2≤1) (m : ℕ) :
    0≤scaledMetricPowerFilter γ J F m ∧ scaledMetricPowerFilter γ J F m≤1 := by
  obtain ⟨h0,h1⟩ := scaled_metric_contraction J F hF hF1 hγ hscale
  exact positive_power_filter_order (1-γ • (J*F*J.adjoint)) (sub_nonneg.mpr h1)
    (sub_le_self 1 h0) m

theorem scaled_metric_source_error (E F Q J K : H→L[ℂ]H)
    (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1) (hF : 0≤F) (hF1 : F≤1)
    (hQ : IsSelfAdjoint Q) (hQQ : Q*Q=Q) (hQ0 : 0≤Q) (hfac : Q=(J*E)*K)
    {C δ γ : ℝ} (hK : ‖K‖≤C) (hδ : ‖F*E-E‖≤δ)
    (hγ : 0<γ) (hscale : γ*‖J‖^2≤1) (m : ℕ) :
    ‖scaledMetricPowerFilter γ J F m*Q-Q‖^2≤
      C^2/(γ*(((2*m:ℕ):ℝ)+1))+3*C^2*δ*‖J‖^2 := by
  let A := 1-γ • (J*F*J.adjoint)
  obtain ⟨hG0,hG1⟩ := scaled_metric_contraction J F hF hF1 hγ.le hscale
  have hA0 : 0≤A := sub_nonneg.mpr hG1
  have hA1 : A≤1 := sub_le_self 1 hG0
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have he : (C^2/γ) • (1-A)=C^2 • (J*F*J.adjoint) := by
    dsimp only [A]
    rw [sub_sub_cancel,smul_smul,div_mul_cancel₀ _ hγ.ne']
  have ho : Q≤(C^2/γ) • (1-A)+(3*C^2*δ*‖J‖^2) • (1:H→L[ℂ]H) := by
    rw [he]
    exact metric_source_projection_order E F Q J K hE hEE hEn hF hQ hQQ hfac hK hδ
  have hh := power_source_projection_error A Q (nonneg_iff_isPositive.mp hA0) hn
    hQ hQQ hQ0 (div_nonneg (sq_nonneg C) hγ.le)
    (by positivity : 0≤3*C^2*δ*‖J‖^2) ho m
  simpa only [scaledMetricPowerFilter,A,div_div] using hh

theorem scaled_metric_image_source_error (L : H≃L[ℂ]H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    [(W.map L.toLinearMap).HasOrthogonalProjection]
    (F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1)
    {δ γ : ℝ} (hδ : ‖F*W.starProjection-W.starProjection‖≤δ)
    (hγ : 0<γ) (hscale : γ*‖L.toContinuousLinearMap‖^2≤1) (m : ℕ) :
    ‖scaledMetricPowerFilter γ L.toContinuousLinearMap F m*(W.map L.toLinearMap).starProjection-
      (W.map L.toLinearMap).starProjection‖^2≤
      ‖L.symm.toContinuousLinearMap‖^2/(γ*(((2*m:ℕ):ℝ)+1))+
      3*‖L.symm.toContinuousLinearMap‖^2*δ*‖L.toContinuousLinearMap‖^2 := by
  apply scaled_metric_source_error W.starProjection F
    (W.map L.toLinearMap).starProjection L.toContinuousLinearMap
    (L.symm.toContinuousLinearMap*(W.map L.toLinearMap).starProjection)
    (isSelfAdjoint_starProjection W) W.isIdempotentElem_starProjection W.starProjection_norm_le hF hF1
    (isSelfAdjoint_starProjection (W.map L.toLinearMap))
    (W.map L.toLinearMap).isIdempotentElem_starProjection
  · exact nonneg_iff_isPositive.mpr ⟨(W.map L.toLinearMap).starProjection_isSymmetric,
      (W.map L.toLinearMap).re_inner_starProjection_nonneg⟩
  · exact metric_image_projection_factorization L W
  · exact metric_image_factor_norm L W
  · exact hδ
  · exact hγ
  · exact hscale

#print axioms scaled_metric_contraction
#print axioms scaledMetricPowerFilter_order
#print axioms scaled_metric_source_error
#print axioms scaled_metric_image_source_error
end QuantitativeMaass
