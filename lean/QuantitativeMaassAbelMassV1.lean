module

public import QuantitativeMaassAbelIntertwiningV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A continuous profile with an upper support bound is integrable on every
right half-line, although it need not have compact support on the full line. -/
theorem integrableOn_Ioi_of_upper_support (f : ℝ → ℂ) (hf : Continuous f)
    (B a : ℝ) (hs : Function.support f⊆Iic B) : IntegrableOn f (Ioi a) := by
  have hi : IntegrableOn f (Ioc a B) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hz : IntegrableOn f (Ioi B) :=
    integrableOn_zero.congr_fun (fun x hx => by
      symm
      by_contra hn
      exact (not_le.mpr hx) (hs hn)) measurableSet_Ioi
  exact (hi.union hz).mono_set Ioi_subset_Ioc_union_Ioi

theorem abelIntegral_integrableOn_Ioi (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (a : ℝ) : IntegrableOn (abelIntegral F) (Ioi a) := by
  obtain ⟨B,_,hB⟩ := hc.isBounded.exists_pos_norm_le
  have hs : Function.support F⊆Iic B := by
    intro q hq
    exact (le_abs_self q).trans (by simpa only [Real.norm_eq_abs] using hB q (subset_tsupport F hq))
  apply integrableOn_Ioi_of_upper_support _ (abelIntegral_smooth F hF hc).continuous B a
  intro q hq
  by_contra h
  exact hq (abelIntegral_zero_above F B q hs (lt_of_not_ge h))

/-- The Abel primitive vanishes at positive infinity by its proved support,
so its derivative integrates to the actual endpoint value. -/
theorem abelIntegral_integral_deriv (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (a : ℝ) :
    (∫ q in Ioi a, abelIntegral (deriv F) q) = -abelIntegral F a := by
  obtain ⟨B,_,hB⟩ := hc.isBounded.exists_pos_norm_le
  have hs : Function.support F⊆Iic B := by
    intro q hq
    exact (le_abs_self q).trans (by simpa only [Real.norm_eq_abs] using hB q (subset_tsupport F hq))
  have ht : Tendsto (abelIntegral F) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop B] with q hq
    exact (abelIntegral_zero_above F B q hs hq).symm
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun q _ => abelIntegral_hasDerivAt F hF hc q)
    (abelIntegral_integrableOn_Ioi (deriv F) (contDiff_infty_iff_deriv.mp hF).2 hc.deriv a) ht

/-- Exact scalar mass normalization, prior to the geometric radial measure
formula. No interchange of non-absolutely-convergent integrals is used. -/
theorem abelProfile_integral_Ioi (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (a : ℝ) :
    (∫ q in Ioi a, abelProfile F q) =
      (Real.sqrt 2/Real.pi:ℂ)*abelIntegral F a := by
  simp only [abelProfile,integral_const_mul,abelIntegral_integral_deriv F hF hc]
  ring

#print axioms abelIntegral_integrableOn_Ioi
#print axioms abelIntegral_integral_deriv
#print axioms abelProfile_integral_Ioi

end QuantitativeMaass
