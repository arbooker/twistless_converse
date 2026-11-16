module

public import QuantitativeMaassScalarRadialBoundV1
public import QuantitativeMaassAbelPuncturedLimitV1
public import QuantitativeMaassPositiveTimeApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

def scalarAbelConvolution (f : ℍ → ℂ) (x : ℍ) (F : ℝ → ℂ) : ℂ :=
  ∫ y : ℍ,abelProfile F (Real.cosh (dist y x))*f y

theorem scalarAbelConvolution_congr (f : ℍ → ℂ) (x : ℍ) (F G : ℝ → ℂ)
    (he : ∀ q,1<q → F q=G q) :
    scalarAbelConvolution f x F=scalarAbelConvolution f x G := by
  apply integral_congr_ae
  filter_upwards with y
  rw [abelProfile_congr_above_one F G he _ (Real.one_le_cosh _)]

theorem scalarAbelConvolution_sub (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R : ℝ) (hR : 0≤R) (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R)) :
    scalarAbelConvolution f x (fun q => F q-G q)=
      scalarAbelConvolution f x F-scalarAbelConvolution f x G := by
  simp only [scalarAbelConvolution,abelProfile_sub F G hF hG hcF hcG,sub_mul]
  exact integral_sub
    (radial_convolution_integrable (abelProfile F) (abelProfile_smooth F hF hcF)
      R hR (abelProfile_support F _ hsF) f hf x)
    (radial_convolution_integrable (abelProfile G) (abelProfile_smooth G hG hcG)
      R hR (abelProfile_support G _ hsG) f hf x)

theorem scalarAbelConvolution_shrinking_bound (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hsR : Function.support F⊆Iic (Real.cosh R))
    (B C D : ℝ) (hB : 1<B) (hD : 0≤D) (hs : Function.support F⊆Iic B)
    (hb : ∀ q,‖deriv F q‖≤C/(B-1))
    (hfD : ∀ y ∈ Metric.closedBall x R,‖f y‖≤D) :
    ‖scalarAbelConvolution f x F‖≤(2*Real.sqrt 2*C*Real.sqrt (B-1))*D := by
  have h := radial_convolution_norm_bound (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hsR) f hf x D hfD
  have hm := abelProfile_small_radius_mass_bound F B (C/(B-1)) hB.le hs hb
  have he : 2*Real.pi*((Real.sqrt 2/Real.pi)*((C/(B-1))*Real.sqrt (B-1))*(B-1))=
      2*Real.sqrt 2*C*Real.sqrt (B-1) := by
    field_simp [Real.pi_ne_zero,ne_of_gt (sub_pos.mpr hB)]
  calc
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right hm hD
    _ = _ := by rw [he]

theorem scalarAbelConvolution_shrinking_tendsto {ι : Type*} (l : Filter ι)
    (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (F : ι → ℝ → ℂ) (hF : ∀ i,ContDiff ℝ ∞ (F i)) (hc : ∀ i,HasCompactSupport (F i))
    (R : ℝ) (hR : 0≤R) (hsR : ∀ i,Function.support (F i)⊆Iic (Real.cosh R))
    (B : ι → ℝ) (C : ℝ) (hB : ∀ i,1<B i) (hlim : Tendsto B l (𝓝 1))
    (hs : ∀ i,Function.support (F i)⊆Iic (B i))
    (hb : ∀ i q,‖deriv (F i) q‖≤C/(B i-1)) :
    Tendsto (fun i => scalarAbelConvolution f x (F i)) l (𝓝 0) := by
  obtain ⟨D,hD,hfD⟩ := continuous_ball_norm_bound f hf x R
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun i => (2*Real.sqrt 2*C*Real.sqrt (B i-1))*D) l (𝓝 0) := by
    simpa only [sub_self,Real.sqrt_zero,mul_zero,zero_mul] using
      (((hlim.sub_const 1).sqrt).const_mul (2*Real.sqrt 2*C)).mul_const D
  exact squeeze_zero (fun i => norm_nonneg _)
    (fun i => scalarAbelConvolution_shrinking_bound f hf x (F i) (hF i) (hc i)
      R hR (hsR i) (B i) C D (hB i) hD (hs i) (hb i) hfD) ht

/-- Removing the q=1 endpoint changes the literal convolution by a term
converging to zero. Only a local bound on the original function is used. -/
theorem scalarAbelBoundary_tendsto {ι : Type*} (l : Filter ι)
    (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => scalarAbelConvolution f x (abelBoundaryPart F (a i))) l (𝓝 0) := by
  obtain ⟨A,hA⟩ := hc.deriv.exists_bound_of_continuous (hF.continuous_deriv (by simp))
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hF.continuous
  obtain ⟨D,hD,hTD⟩ := smoothTransition_deriv_bounded
  have hA0 : 0≤A := (norm_nonneg (deriv F 0)).trans (hA 0)
  have hB0 : 0≤B := (norm_nonneg (F 0)).trans (hB 0)
  have hlim : Tendsto (fun i => 1+2*a i) l (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (ha0.const_mul 2).const_add 1
  apply scalarAbelConvolution_shrinking_tendsto l f hf x (fun i => abelBoundaryPart F (a i))
    (fun i => abelBoundaryPart_smooth F hF (a i))
    (fun i => abelBoundaryPart_compact F hc (a i)) R hR
    (fun i => abelBoundaryPart_support_source F (a i) _ hs)
    (fun i => 1+2*a i) (2*(A+2*B*D)) (fun i => by have := ha i; linarith) hlim
    (fun i => abelBoundaryPart_support F (a i) (ha i))
  intro i q
  have he : 2*(A+2*B*D)/(1+2*a i-1)=(A+2*B*D)/a i := by
    rw [show 1+2*a i-1=2*a i by ring]
    field_simp
  rw [he]
  exact abelBoundaryPart_derivative_bound F hF A B D hA0 hB0 hD hA hB hTD
    (a i) (ha i) (ha1 i) q

theorem scalarAbelPunctured_eq (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    scalarPositiveAbel f x (abelPuncturedPositiveTest F hF hr R hR hs a ha ha1)=
      scalarAbelConvolution f x F-scalarAbelConvolution f x (abelBoundaryPart F a) := by
  change scalarAbelConvolution f x
    (coshTestLift (positiveCoshTest (fun q => F q-abelBoundaryPart F a q)))=_
  rw [scalarAbelConvolution_congr f x _ (fun q => F q-abelBoundaryPart F a q)
    (coshTestLift_positiveCoshTest _)]
  exact scalarAbelConvolution_sub f hf x F (abelBoundaryPart F a) hF
    (abelBoundaryPart_smooth F hF a) hc (abelBoundaryPart_compact F hc a) R hR hs
    (abelBoundaryPart_support_source F a _ hs)

#print axioms scalarAbelConvolution_congr
#print axioms scalarAbelConvolution_sub
#print axioms scalarAbelConvolution_shrinking_bound
#print axioms scalarAbelConvolution_shrinking_tendsto
#print axioms scalarAbelBoundary_tendsto
#print axioms scalarAbelPunctured_eq

end QuantitativeMaass
