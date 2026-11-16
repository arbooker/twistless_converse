module

public import QuantitativeMaassColumnLinearTraceV1
public import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open ContinuousLinearMap MeasureTheory
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace α]

omit [CompleteSpace H] in
theorem columnLinearTrace_mono (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T S : H→L[ℂ]H) (h : T≤S) : columnLinearTrace μ c T≤columnLinearTrace μ c S := by
  apply integral_mono (columnLinearTrace_integrable μ c hc T) (columnLinearTrace_integrable μ c hc S)
  intro x
  have hh := (nonneg_iff_isPositive.mp (sub_nonneg.mpr h)).re_inner_nonneg_left (c x)
  change 0≤(inner ℂ ((S-T) (c x)) (c x)).re at hh
  simpa only [sub_apply,inner_sub_left,Complex.sub_re,sub_nonneg] using hh

/-- Approximate preservation of an orthogonal projection by a positive
operator gives a coefficient-one upper trace bound, with linear error. -/
theorem columnLinearTrace_projection_approx_fixed (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (E F : H→L[ℂ]H) (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1)
    (hF : 0≤F) {δ : ℝ} (hδ : ‖F*E-E‖≤δ) :
    columnLinearTrace μ c E≤columnLinearTrace μ c F+3*δ*(∫ x,‖c x‖^2 ∂μ) := by
  have hFs := (nonneg_iff_isPositive.mp hF).isSelfAdjoint
  let D := F-(1-E)*F*(1-E)
  have ha : (F*E-E).adjoint=E*F-E := by
    simp only [map_sub,mul_def,adjoint_comp,hE.adjoint_eq,hFs.adjoint_eq]
  have hd : D-E=(F*E-E)+(F*E-E).adjoint-E*(F*E-E) := by
    rw [ha,mul_sub,hEE]
    dsimp only [D]
    noncomm_ring
  have hnorm : ‖D-E‖≤3*δ := by
    rw [hd]
    have hm : ‖E*(F*E-E)‖≤δ := (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right hEn (norm_nonneg _)).trans (by simpa only [one_mul] using hδ))
    have haa : ‖(F*E-E).adjoint‖≤δ := by rw [adjoint.norm_map]; exact hδ
    have hh := (norm_sub_le ((F*E-E)+(F*E-E).adjoint) (E*(F*E-E))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    linarith
  have hp : 0≤(1-E)*F*(1-E) := by
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj (1-E)
    have hs : (1-E).adjoint=1-E := by rw [map_sub,adjoint_one,hE.adjoint_eq]
    exact nonneg_iff_isPositive.mpr (by simpa only [hs,←mul_def,mul_assoc] using hh)
  have hDF : D≤F := sub_le_self F hp
  have htrace := columnLinearTrace_mono μ c hc D F hDF
  have he := columnLinearTrace_approx μ c hc D E hnorm
  have hab := (abs_le.mp he).1
  linarith

/-- The canonical subtraction is retained exactly while replacing only
the original source projection by its finite positive filter. -/
theorem columnLinearTrace_excess_approx_fixed (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (E F Q : H→L[ℂ]H) (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1)
    (hF : 0≤F) {δ : ℝ} (hδ : ‖F*E-E‖≤δ) :
    columnLinearTrace μ c (E-Q)≤columnLinearTrace μ c (F-Q)+3*δ*(∫ x,‖c x‖^2 ∂μ) := by
  rw [columnLinearTrace_sub μ c hc E Q,columnLinearTrace_sub μ c hc F Q]
  have hh := columnLinearTrace_projection_approx_fixed μ c hc E F hE hEE hEn hF hδ
  linarith

#print axioms columnLinearTrace_mono
#print axioms columnLinearTrace_projection_approx_fixed
#print axioms columnLinearTrace_excess_approx_fixed
end QuantitativeMaass
