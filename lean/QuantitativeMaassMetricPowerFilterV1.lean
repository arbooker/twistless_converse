module

public import QuantitativeMaassMetricFilterTransportV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_power_filter_order (A : H→L[ℂ]H) (hA : 0≤A) (hA1 : A≤1) (m : ℕ) :
    0≤1-A^m ∧ 1-A^m≤1 := by
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA).mpr hA1
  have hpow : ‖A^m‖≤1 := by
    by_cases hm : m=0
    · subst m
      exact norm_id_le
    · exact (norm_pow_le' A (Nat.pos_of_ne_zero hm)).trans
        (pow_le_one₀ (norm_nonneg A) hn)
  have h0 := CStarAlgebra.pow_nonneg A m hA
  exact ⟨sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp hpow),
    sub_le_self 1 h0⟩

def metricPowerFilter (J F : H→L[ℂ]H) (m : ℕ) : H→L[ℂ]H :=
  1-(1-metricPositiveFilter J F)^m

theorem metricPowerFilter_order (J F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1) (m : ℕ) :
    0≤metricPowerFilter J F m ∧ metricPowerFilter J F m≤1 := by
  obtain ⟨h0,h1⟩ := metricPositiveFilter_order J F hF hF1
  exact positive_power_filter_order (1-metricPositiveFilter J F) (sub_nonneg.mpr h1)
    (sub_le_self 1 h0) m

/-- A literal finite positive polynomial approximately fixes the transformed
source, with explicit degree and original-source error. Invertibility of
the metric enters through the bounded factorization rather than an axiom. -/
theorem metricPowerFilter_source_error (E F Q J K : H→L[ℂ]H)
    (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1) (hF : 0≤F) (hF1 : F≤1)
    (hQ : IsSelfAdjoint Q) (hQQ : Q*Q=Q) (hQ0 : 0≤Q) (hfac : Q=(J*E)*K)
    {C δ : ℝ} (hK : ‖K‖≤C) (hδ : ‖F*E-E‖≤δ) (m : ℕ) :
    ‖metricPowerFilter J F m*Q-Q‖^2≤
      C^2/(metricFilterScale J*(((2*m:ℕ):ℝ)+1))+3*C^2*δ*‖J‖^2 := by
  let A := 1-metricPositiveFilter J F
  obtain ⟨hG0,hG1⟩ := metricPositiveFilter_order J F hF hF1
  have hA0 : 0≤A := sub_nonneg.mpr hG1
  have hA1 : A≤1 := sub_le_self 1 hG0
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hA0).mpr hA1
  have hs : 0<metricFilterScale J := metricFilterScale_pos J
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have he : (C^2/metricFilterScale J) • (1-A)=C^2 • (J*F*J.adjoint) := by
    dsimp only [A]
    rw [sub_sub_cancel]
    unfold metricPositiveFilter
    rw [smul_smul,div_mul_cancel₀ _ hs.ne']
  have ho : Q≤(C^2/metricFilterScale J) • (1-A)+
      (3*C^2*δ*‖J‖^2) • (1:H→L[ℂ]H) := by
    rw [he]
    exact metric_source_projection_order E F Q J K hE hEE hEn hF hQ hQQ hfac hK hδ
  have hh := power_source_projection_error A Q (nonneg_iff_isPositive.mp hA0) hn
    hQ hQQ hQ0 (div_nonneg (sq_nonneg C) hs.le)
    (by positivity : 0≤3*C^2*δ*‖J‖^2) ho m
  simpa only [metricPowerFilter,A,div_div] using hh

#print axioms positive_power_filter_order
#print axioms metricPowerFilter_order
#print axioms metricPowerFilter_source_error
end QuantitativeMaass
