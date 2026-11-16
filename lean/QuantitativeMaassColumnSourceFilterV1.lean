module

public import QuantitativeMaassMetricSourceOrderV1
public import QuantitativeMaassColumnTraceLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap MeasureTheory
namespace QuantitativeMaass
variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Intertwining of cograms through an isometric ambient embedding. -/
theorem isometric_source_projection_intertwines
    {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (J : H→ₗᵢ[ℂ]G) (U : V→L[ℂ]H) (W : V→L[ℂ]G) (T : V→L[ℂ]V)
    (h : J.toContinuousLinearMap.comp U=W) :
    (W.comp (T.comp W.adjoint)).comp J.toContinuousLinearMap=
      J.toContinuousLinearMap.comp (U.comp (T.comp U.adjoint)) := by
  rw [←h,adjoint_comp]
  simp only [comp_assoc,J.adjoint_comp_self,one_def,comp_id]

/-- Source recovery survives compression by an isometry. -/
theorem isometric_filter_source_error
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (J : H→ₗᵢ[ℂ]G) (Q : H→L[ℂ]H) (P F : G→L[ℂ]G)
    (hQn : ‖Q‖≤1)
    (hfix : P.comp (J.toContinuousLinearMap.comp Q)=J.toContinuousLinearMap.comp Q)
    {δ : ℝ} (hδ : ‖F*P-P‖≤δ) :
    ‖(J.toContinuousLinearMap.adjoint.comp (F.comp J.toContinuousLinearMap))*Q-Q‖≤δ := by
  let Z := J.toContinuousLinearMap
  have hZ : Z.adjoint.comp Z=1 := J.adjoint_comp_self
  change P.comp (Z.comp Q)=Z.comp Q at hfix
  have he : (Z.adjoint.comp (F.comp Z))*Q-Q=
      Z.adjoint.comp ((F*P-P).comp (Z.comp Q)) := by
    simp only [sub_comp,comp_sub,mul_def,comp_assoc,hfix]
    rw [←comp_assoc Z.adjoint Z,hZ]
    rfl
  have hZn : ‖Z‖≤1 := J.norm_toContinuousLinearMap_le
  have hZan : ‖Z.adjoint‖≤1 := by rw [adjoint.norm_map];exact hZn
  have hZQn : ‖Z.comp Q‖≤1 := (opNorm_comp_le _ _).trans
    ((mul_le_mul hZn hQn (norm_nonneg _) (by norm_num)).trans (by norm_num))
  rw [he]
  calc
    _ ≤ ‖Z.adjoint‖*(‖F*P-P‖*‖Z.comp Q‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(δ*1) := mul_le_mul hZan
      (mul_le_mul hδ hZQn (norm_nonneg _) ((norm_nonneg _).trans hδ))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = δ := by ring

/-- Approximate source preservation bounds the actual canonical excess
column trace. The canonical projection keeps coefficient one. -/
theorem column_source_filter_excess (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (W : Submodule ℂ H) [CompleteSpace W] (F Qcan D : H→L[ℂ]H)
    (hF : 0≤F) {δ : ℝ} (hδ : ‖F*W.starProjection-W.starProjection‖≤δ) :
    columnLinearTrace μ c (D*W.starProjection*D.adjoint-D*Qcan*D.adjoint)≤
      columnLinearTrace μ c (D*(F-Qcan)*D.adjoint)+
        (3*δ*‖D‖^2)*(∫ x,‖c x‖^2 ∂μ) := by
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have hsrc := projection_le_of_approx_fixed W.starProjection F
    (isSelfAdjoint_starProjection W) W.isIdempotentElem_starProjection
    W.starProjection_norm_le hF hδ
  have hdiff : W.starProjection-F≤(3*δ) • (1:H→L[ℂ]H) := by
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hsrc)
  have hconj := star_left_conjugate_le_conjugate hdiff D.adjoint
  change D.adjoint.adjoint*(W.starProjection-F)*D.adjoint≤
    D.adjoint.adjoint*((3*δ) • (1:H→L[ℂ]H))*D.adjoint at hconj
  rw [adjoint_adjoint] at hconj
  simp only [mul_smul_comm,smul_mul_assoc,mul_one] at hconj
  let T := D*W.starProjection*D.adjoint-D*Qcan*D.adjoint
  let S := D*(F-Qcan)*D.adjoint
  have he : T-S=D*(W.starProjection-F)*D.adjoint := by
    dsimp only [T,S]
    noncomm_ring
  have hh := columnLinearTrace_mono μ c hc (T-S) ((3*δ) • (D*D.adjoint))
    (by rw [he];exact hconj)
  have hn : ‖(3*δ) • (D*D.adjoint)‖≤3*δ*‖D‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hd : ‖D*D.adjoint‖≤‖D‖^2 := by
      simpa only [adjoint.norm_map,pow_two] using norm_mul_le D D.adjoint
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have hb := (le_abs_self _).trans ((columnLinearTrace_bound μ c hc ((3*δ) • (D*D.adjoint))).trans
    (mul_le_mul_of_nonneg_right hn (integral_nonneg (fun _ => sq_nonneg _))))
  rw [columnLinearTrace_sub μ c hc T S] at hh
  simpa only [add_comm] using sub_le_iff_le_add.mp (hh.trans hb)

#print axioms isometric_source_projection_intertwines
#print axioms isometric_filter_source_error
#print axioms column_source_filter_excess
end QuantitativeMaass
