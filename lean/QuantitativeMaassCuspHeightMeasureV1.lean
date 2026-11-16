module

public import AsymptoticHyperbolicAreaV1
public import QuantitativeMaassFrequencyTailDilationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped ENNReal NNReal

namespace QuantitativeMaass

/-- Integration of a height-dependent nonnegative function over the actual
closed cusp strip uses precisely the measure dy/y squared. -/
theorem lintegral_highStrip_height (g : ℝ→ℝ≥0∞) (hg : Measurable g)
    (H : ℝ) (hH : 0<H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,g z.im)=
      ∫⁻ y in Ici H,g y/(ENNReal.ofReal y)^2 := by
  have hm : Measurable (fun z : ℍ => (↑((1/NNReal.mk z.im z.im_pos.le)^2 : ℝ≥0) : ℝ≥0∞)) := by
    fun_prop
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  have hgm : Measurable (fun z : ℍ => g z.im) := hg.comp continuous_im.measurable
  rw [UpperHalfPlane.volume_def,setLIntegral_withDensity_eq_setLIntegral_mul _ hm
    hgm (AsymptoticHyperbolicArea.closedTerminal_measurable H)]
  have he : (fun z : ℍ => (↑((1/NNReal.mk z.im z.im_pos.le)^2 : ℝ≥0) : ℝ≥0∞)*g z.im)=
      fun z : ℍ => (↑((1/‖(z:ℂ).im‖₊)^2 : ℝ≥0) : ℝ≥0∞)*g (z:ℂ).im := by
    funext z
    simp only [coe_im,Real.nnnorm_of_nonneg z.im_pos.le]
  change (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
    (↑((1/NNReal.mk z.im z.im_pos.le)^2 : ℝ≥0) : ℝ≥0∞)*g z.im
    ∂volume.comap UpperHalfPlane.coe)=_
  rw [he,hp.setLIntegral_comp_emb measurableEmbedding_coe
    (fun w : ℂ => (↑((1/‖w.im‖₊)^2 : ℝ≥0) : ℝ≥0∞)*g w.im)
    (AsymptoticHyperbolicArea.closedTerminal H)]
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_left.mpr (Set.image_subset_range _ _)]
  rw [AsymptoticHyperbolicArea.closedTerminal_image hH]
  rw [←(Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ×ℝ in Ico (0:ℝ) 1 ×ˢ Ici H,
    (↑((1/‖p.2‖₊)^2 : ℝ≥0) : ℝ≥0∞)*g p.2)=_
  rw [Measure.volume_eq_prod,setLIntegral_prod _ (by fun_prop)]
  have hv : (∫⁻ y in Ici H,(↑((1/‖y‖₊)^2 : ℝ≥0) : ℝ≥0∞)*g y)=
      ∫⁻ y in Ici H,g y/(ENNReal.ofReal y)^2 := by
    apply setLIntegral_congr_fun measurableSet_Ici
    intro y hy
    have hy0 : 0<y := hH.trans_le hy
    have hn : (NNReal.mk y hy0.le)≠0 := by
      intro hh
      have hh' := congrArg (fun a : ℝ≥0 => (a:ℝ)) hh
      exact hy0.ne' hh'
    simp only [Real.nnnorm_of_nonneg hy0.le,div_eq_mul_inv,one_mul]
    rw [ENNReal.coe_pow,ENNReal.coe_inv hn,ENNReal.ofReal_eq_coe_nnreal hy0.le,ENNReal.inv_pow,mul_comm]
  simp only [hv]
  simp

#print axioms lintegral_highStrip_height

end QuantitativeMaass
