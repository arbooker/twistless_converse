module

public import QuantitativeMaassAbelSmallRadiusBoundV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A derivative of size C/(B-1) still gives a vanishing operator bound
when the radial q-support shrinks to one. -/
theorem abelKernelOperator_shrinking_support_bound (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hsR : Function.support F⊆Iic (Real.cosh R))
    (B C : ℝ) (hB : 1<B) (hs : Function.support F⊆Iic B)
    (hb : ∀ q,‖deriv F q‖≤C/(B-1)) :
    ‖abelKernelOperator N F hF hc R hR hsR‖≤2*Real.sqrt 2*C*Real.sqrt (B-1) := by
  have h := (radialKernelOperator_norm N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hsR)).trans
      (abelProfile_small_radius_mass_bound F B (C/(B-1)) hB.le hs hb)
  calc
    _ ≤ _ := h
    _ = _ := by
      field_simp [Real.pi_ne_zero,ne_of_gt (sub_pos.mpr hB)]

/-- Shrinking q-support and the explicit reciprocal-width derivative bound
force operator-norm convergence to zero. The tests themselves may vary. -/
theorem abelKernelOperator_shrinking_support_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) [NeZero N] (F : ι → ℝ → ℂ) (hF : ∀ i,ContDiff ℝ ∞ (F i))
    (hc : ∀ i,HasCompactSupport (F i)) (R : ι → ℝ) (hR : ∀ i,0≤R i)
    (hsR : ∀ i,Function.support (F i)⊆Iic (Real.cosh (R i)))
    (B : ι → ℝ) (C : ℝ) (hB : ∀ i,1<B i) (hlim : Tendsto B l (𝓝 1))
    (hs : ∀ i,Function.support (F i)⊆Iic (B i))
    (hb : ∀ i q,‖deriv (F i) q‖≤C/(B i-1)) :
    Tendsto (fun i => abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i)) l (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f := fun i => abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i))).mpr
  have ht : Tendsto (fun i => 2*Real.sqrt 2*C*Real.sqrt (B i-1)) l (𝓝 0) := by
    simpa only [sub_self,Real.sqrt_zero,mul_zero] using
      ((hlim.sub_const 1).sqrt).const_mul (2*Real.sqrt 2*C)
  exact squeeze_zero
    (fun i => norm_nonneg (abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i)))
    (fun i => abelKernelOperator_shrinking_support_bound N (F i) (hF i) (hc i)
      (R i) (hR i) (hsR i) (B i) C (hB i) (hs i) (hb i)) ht

#print axioms abelKernelOperator_shrinking_support_bound
#print axioms abelKernelOperator_shrinking_support_tendsto

end QuantitativeMaass
