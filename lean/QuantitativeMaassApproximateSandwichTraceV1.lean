module

public import QuantitativeMaassApproximateProjectionTraceV1
public import AsymptoticObservationPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open ContinuousLinearMap MeasureTheory
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace α]

theorem columnLinearTrace_sandwich (μ : Measure α) (c : α→H) (R T : H→L[ℂ]H) :
    columnLinearTrace μ c (R.comp (T.comp R.adjoint))=
      columnLinearTrace μ (fun x => R.adjoint (c x)) T := by
  apply integral_congr_ae
  filter_upwards with x
  exact congrArg Complex.re ((R.adjoint_inner_right (T (R.adjoint (c x))) (c x)).symm)

theorem adjoint_column_energy_le (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (R : H→L[ℂ]H) (hR : ‖R‖≤1) :
    (∫ x,‖R.adjoint (c x)‖^2 ∂μ)≤∫ x,‖c x‖^2 ∂μ := by
  have hd := hc.continuousLinearMap_comp R.adjoint
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd)
    ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc)
  intro x
  apply pow_le_pow_left₀ (norm_nonneg _)
  have hRa : ‖R.adjoint‖≤1 := by rw [adjoint.norm_map]; exact hR
  exact (R.adjoint.le_opNorm _).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hRa (norm_nonneg (c x)))

/-- Finite reconstruction and a positive approximate identity can replace
an exact reconstructed source projection with no leading-factor loss. -/
theorem columnLinearTrace_sandwich_approx_fixed (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (E F R S Q : H→L[ℂ]H) (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1)
    (hF : 0≤F) (hFn : ‖F‖≤1) (hR : ‖R‖≤1) (hS : ‖S‖≤1)
    {δ η : ℝ} (hδ : ‖F*E-E‖≤δ) (hη : ‖R-S‖≤η) :
    columnLinearTrace μ c (R.comp (E.comp R.adjoint)-Q)≤
      columnLinearTrace μ c (S.comp (F.comp S.adjoint)-Q)+(3*δ+2*η)*(∫ x,‖c x‖^2 ∂μ) := by
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have hp := columnLinearTrace_projection_approx_fixed μ (fun x => R.adjoint (c x))
    (hc.continuousLinearMap_comp R.adjoint) E F hE hEE hEn hF hδ
  rw [←columnLinearTrace_sandwich μ c R E,←columnLinearTrace_sandwich μ c R F] at hp
  have hb := mul_le_mul_of_nonneg_left (adjoint_column_energy_le μ c hc R hR)
    (by positivity : 0≤3*δ)
  have hs : ‖R.comp (F.comp R.adjoint)-S.comp (F.comp S.adjoint)‖≤2*η := by
    have hh := AsymptoticObservation.sandwich_sub_norm_le R S F F hFn hFn
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    exact hh.trans (mul_le_mul (by linarith : ‖R‖+‖S‖≤2) hη
      (norm_nonneg _) (by norm_num : (0:ℝ)≤2))
  have ht := (abs_le.mp (columnLinearTrace_approx μ c hc _ _ hs)).2
  rw [columnLinearTrace_sub μ c hc _ Q,columnLinearTrace_sub μ c hc _ Q]
  nlinarith only [hp,hb,ht]

#print axioms columnLinearTrace_sandwich
#print axioms adjoint_column_energy_le
#print axioms columnLinearTrace_sandwich_approx_fixed
end QuantitativeMaass
