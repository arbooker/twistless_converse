module

public import QuantitativeMaassMetricSourceOrderV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cogram_le_norm_square (J : H→L[ℂ]H) :
    J*J.adjoint≤‖J‖^2 • (1:H→L[ℂ]H) := by
  have hp : 0≤J*J.adjoint := by
    simpa only [adjoint_adjoint,mul_def] using
      nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self J.adjoint)
  have hn : ‖J*J.adjoint‖≤‖J‖^2 := by
    simpa only [adjoint.norm_map,pow_two] using norm_mul_le J J.adjoint
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _) hp).mp hn

/-- Transport of approximate source preservation by an arbitrary bounded
metric map. The factorization is the actual transformed range, and its
bounded inverse enters only the explicit constants. -/
theorem metric_source_projection_order (E F Q J K : H→L[ℂ]H)
    (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1) (hF : 0≤F)
    (hQ : IsSelfAdjoint Q) (hQQ : Q*Q=Q) (hfac : Q=(J*E)*K)
    {C δ : ℝ} (hK : ‖K‖≤C) (hδ : ‖F*E-E‖≤δ) :
    Q≤C^2 • (J*F*J.adjoint)+(3*C^2*δ*‖J‖^2) • (1:H→L[ℂ]H) := by
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have hbase := projection_le_cogram_of_factorization Q (J*E) K hQ hQQ hfac hK
  have he : (J*E)*(J*E).adjoint=J*E*J.adjoint := by
    rw [show (J*E).adjoint=E*J.adjoint by
      simp only [mul_def,adjoint_comp,hE.adjoint_eq]]
    calc
      _ = J*(E*E)*J.adjoint := by noncomm_ring
      _ = _ := by rw [hEE]
  rw [he] at hbase
  have hc := star_left_conjugate_le_conjugate
    (projection_le_of_approx_fixed E F hE hEE hEn hF hδ) J.adjoint
  change J.adjoint.adjoint*E*J.adjoint≤
    J.adjoint.adjoint*(F+(3*δ) • (1:H→L[ℂ]H))*J.adjoint at hc
  rw [adjoint_adjoint] at hc
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one] at hc
  have hh := smul_le_smul_of_nonneg_left (cogram_le_norm_square J)
    (mul_nonneg (by norm_num : (0:ℝ)≤3) hδ0)
  have hm := hc.trans (add_le_add le_rfl hh)
  have ht := hbase.trans (smul_le_smul_of_nonneg_left hm (sq_nonneg C))
  simpa only [smul_add,smul_smul,show C^2*(3*δ*‖J‖^2)=3*C^2*δ*‖J‖^2 by ring] using ht

def metricFilterScale (J : H→L[ℂ]H) : ℝ := (‖J‖^2+1)⁻¹

omit [CompleteSpace H] in
theorem metricFilterScale_pos (J : H→L[ℂ]H) : 0<metricFilterScale J := by
  unfold metricFilterScale
  positivity

def metricPositiveFilter (J F : H→L[ℂ]H) : H→L[ℂ]H :=
  metricFilterScale J • (J*F*J.adjoint)

theorem metricPositiveFilter_order (J F : H→L[ℂ]H) (hF : 0≤F) (hF1 : F≤1) :
    0≤metricPositiveFilter J F ∧ metricPositiveFilter J F≤1 := by
  have hp : 0≤J*F*J.adjoint := by
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj J.adjoint
    simpa only [adjoint_adjoint,←mul_def,mul_assoc] using nonneg_iff_isPositive.mpr hh
  have h0 : 0≤metricPositiveFilter J F :=
    smul_nonneg (metricFilterScale_pos J).le hp
  have hc := star_left_conjugate_le_conjugate hF1 J.adjoint
  change J.adjoint.adjoint*F*J.adjoint≤J.adjoint.adjoint*1*J.adjoint at hc
  rw [adjoint_adjoint,mul_one] at hc
  have hb := smul_le_smul_of_nonneg_left (hc.trans (cogram_le_norm_square J))
    (metricFilterScale_pos J).le
  have hs : metricFilterScale J*‖J‖^2≤1 := by
    have he : metricFilterScale J*(‖J‖^2+1)=1 := inv_mul_cancel₀ (by positivity)
    nlinarith [metricFilterScale_pos J]
  have ht : (metricFilterScale J*‖J‖^2) • (1:H→L[ℂ]H)≤1 := by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right hs
      (zero_le_one : (0:H→L[ℂ]H)≤1)
  have hb' : metricPositiveFilter J F≤(metricFilterScale J*‖J‖^2) • (1:H→L[ℂ]H) := by
    simpa only [metricPositiveFilter,smul_smul] using hb
  exact ⟨h0,hb'.trans ht⟩

#print axioms cogram_le_norm_square
#print axioms metric_source_projection_order
#print axioms metricPositiveFilter_order
end QuantitativeMaass
