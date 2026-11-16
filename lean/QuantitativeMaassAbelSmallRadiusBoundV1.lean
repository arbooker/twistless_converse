module

public import QuantitativeMaassAbelOperatorBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The true square-root length of the Abel integration interval gives a
bound that vanishes with the radial support radius. -/
theorem abelIntegral_small_radius_bound (f : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support f⊆Iic B) (hb : ∀ q,‖f q‖≤C) (q : ℝ) (hq : 1≤q) :
    ‖abelIntegral f q‖≤C*(Real.sqrt (B-1)) := by
  have he : abelIntegral f q=∫ s in Ioc (0:ℝ) (Real.sqrt (B-1)),f (q+s^2) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ h => h.1)
    intro s hs'
    have hlow : 0<s := hs'.1
    have hhigh : Real.sqrt (B-1)<s := by
      by_contra hn
      exact hs'.2 ⟨hlow,le_of_not_gt hn⟩
    by_contra hn
    have hh := hs hn
    change q+s^2≤B at hh
    have hsqrt := Real.sq_sqrt (sub_nonneg.mpr hB)
    nlinarith [Real.sqrt_nonneg (B-1),sq_nonneg (s-Real.sqrt (B-1))]
  rw [he]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (0:ℝ) (Real.sqrt (B-1)))
    (f:=fun s => f (q+s^2)) (by simp) (fun s _ => hb (q+s^2))
  simpa only [Real.volume_real_Ioc_of_le (Real.sqrt_nonneg (B-1)),sub_zero] using h

theorem abelProfile_small_radius_bound (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,‖deriv F q‖≤C) (q : ℝ) (hq : 1≤q) :
    ‖abelProfile F q‖≤(Real.sqrt 2/Real.pi)*(C*(Real.sqrt (B-1))) := by
  have hs' : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have h := abelIntegral_small_radius_bound (deriv F) B C hB hs' hb q hq
  rw [abelProfile,norm_mul,norm_neg]
  have hn : ‖(Real.sqrt 2/Real.pi:ℂ)‖=Real.sqrt 2/Real.pi := by
    rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)

/-- The Schur mass is bounded by the three-halves power of B-1 times
the first-derivative bound. This improves the estimate near time zero. -/
theorem abelProfile_small_radius_mass_bound (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,‖deriv F q‖≤C) :
    2*Real.pi*(∫ q in Ioi (1:ℝ),‖abelProfile F q‖)≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(Real.sqrt (B-1)))*(B-1)) := by
  have he : (∫ q in Ioi (1:ℝ),‖abelProfile F q‖)=∫ q in Ioc (1:ℝ) B,‖abelProfile F q‖ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
    intro q hq
    have hhigh : B<q := by
      by_contra hn
      exact hq.2 ⟨hq.1,le_of_not_gt hn⟩
    have hz : abelProfile F q=0 := by
      by_contra hn
      exact (not_le_of_gt hhigh) (abelProfile_support F B hs hn)
    rw [hz,norm_zero]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (1:ℝ) B)
    (f:=fun q => ‖abelProfile F q‖) (by simp) (fun q hq => by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact abelProfile_small_radius_bound F B C hB hs hb q hq.1.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
    Real.volume_real_Ioc_of_le hB] at h
  rw [he]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem abelKernelOperator_small_radius_bound (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (C : ℝ) (hb : ∀ q,‖deriv F q‖≤C) :
    ‖abelKernelOperator N F hF hc R hR hs‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(Real.sqrt (Real.cosh R-1)))*(Real.cosh R-1)) :=
  (radialKernelOperator_norm N (abelProfile F) (abelProfile_smooth F hF hc) R hR
    (abelProfile_support F _ hs)).trans
      (abelProfile_small_radius_mass_bound F _ C (Real.one_le_cosh R) hs hb)

#print axioms abelIntegral_small_radius_bound
#print axioms abelProfile_small_radius_bound
#print axioms abelProfile_small_radius_mass_bound
#print axioms abelKernelOperator_small_radius_bound

end QuantitativeMaass
