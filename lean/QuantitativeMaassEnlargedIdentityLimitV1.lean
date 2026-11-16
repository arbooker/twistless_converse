module

public import QuantitativeMaassEnlargedIdentityBoundV1
public import QuantitativeMaassTrimmedIdentityLimitV1
public import QuantitativeMaassLogPowerMarginV1
public import QuantitativeMaassLogPowerExceptionalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual enlarged-window identity error is negligible relative to the
original, original main-term normalization. -/
theorem windowIdentityContribution_enlarged_scaled_negligible
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      ‖windowIdentityContribution K hc (R t) (hRp t) (t-δ t) (t+ε t+δ t)-
        ((t*ε t/(2*Real.pi):ℝ):ℂ)‖/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := windowIdentityContribution_enlarged_bound K he hc hK hm
  have hi : Tendsto (fun t => 1/(t*ε t)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (center_mul_width_tendsto ε (hε.mono (fun _ h => h.1)) hproduct)
  have hmajor : Tendsto (fun t => C*(δ t/ε t+1/(t*ε t))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hsmall.add hi).const_mul C
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (norm_nonneg _) (mul_pos ht he.1).le
  · filter_upwards [hε,hδ,hR1,hRδ,eventually_ge_atTop (1:ℝ)] with t he hd hr hrd ht
    have ht0 : 0<t := by linarith
    have hh := hbound t (ε t) (δ t) (R t) (hRp t) ht ⟨he.1.le,he.2⟩ hd.1 hd.2 hr hrd
    calc
      _ ≤ C*(t*δ t+1)/(t*ε t) := div_le_div_of_nonneg_right hh (mul_pos ht0 he.1).le
      _ = _ := by field_simp

theorem windowIdentityContribution_enlarged_normalized
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t) (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRδ : ∀ᶠ t in atTop,1/R t≤δ t)
    (hsmall : Tendsto (fun t => δ t/ε t) atTop (𝓝 0))
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (windowIdentityContribution K hc (R t) (hRp t)
      (t-δ t) (t+ε t+δ t)).re/(t*ε t)) atTop (𝓝 (1/(2*Real.pi))) := by
  have hscaled := windowIdentityContribution_enlarged_scaled_negligible K he hc hK hm
    ε hε δ hδ R hRp hR1 hRδ hsmall hproduct
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hscaled
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t het ht
  let I := windowIdentityContribution K hc (R t) (hRp t) (t-δ t) (t+ε t+δ t)
  have hid : I.re/(t*ε t)-1/(2*Real.pi)=
      (I-((t*ε t/(2*Real.pi):ℝ):ℂ)).re/(t*ε t) := by
    simp only [Complex.sub_re,Complex.ofReal_re]
    field_simp [Real.pi_ne_zero,ht.ne',het.1.ne']
  change ‖I.re/(t*ε t)-1/(2*Real.pi)‖≤_
  rw [hid,Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos ht het.1)]
  exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (mul_pos ht het.1).le


#print axioms windowIdentityContribution_enlarged_scaled_negligible
#print axioms windowIdentityContribution_enlarged_normalized

end QuantitativeMaass
