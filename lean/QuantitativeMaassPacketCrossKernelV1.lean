module

public import QuantitativeMaassReflectionCovarianceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap

namespace QuantitativeMaass

/-- An invariant AE equality for the actual quotient measure holds AE for
hyperbolic volume. Every orbit meets the positive part of its normalized density. -/
theorem invariant_ae_eq_volume (N : ℕ) (f g : ℍ → ℂ)
    (hf : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (hg : ∀ γ : gamma N,∀ z,g (γ•z)=g z)
    (he : f=ᵐ[quotientMeasure N]g) : f=ᵐ[volume]g := by
  have h0 : ∀ᵐ z : ℍ ∂volume,density N z≠0 → f z=g z :=
    (ae_withDensity_iff (density_measurable N)).mp he
  have hγ (γ : gamma N) : ∀ᵐ z : ℍ ∂volume,
      density N (γ•z)≠0 → f (γ•z)=g (γ•z) :=
    (AsymptoticRationalGroup.measurePreserving γ.val).quasiMeasurePreserving.ae h0
  filter_upwards [ae_all_iff.mpr hγ] with z hz
  by_contra hn
  have hzero (γ : gamma N) : density N (γ•z)=0 := by
    by_contra hd
    exact hn (by simpa only [hf,hg] using hz γ hd)
  have hsum := density_orbit_sum N z
  change (∑' γ : gamma N,density N (γ•z))=1 at hsum
  simp_rw [hzero] at hsum
  simp only [tsum_zero,zero_ne_one] at hsum

/-- Continuous invariant representatives agree everywhere once they agree
on the actual quotient almost everywhere. No support-invariance assumption. -/
theorem continuous_invariant_eq_of_ae (N : ℕ) (f g : ℍ → ℂ)
    (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (hg : ∀ γ : gamma N,∀ z,g (γ•z)=g z)
    (he : f=ᵐ[quotientMeasure N]g) : f=g :=
  Measure.eq_of_ae_eq (invariant_ae_eq_volume N f g hf hg he) hfc hgc

/-- The actual square kernel is the cross inner product of continuous
invariant columns at EVERY pair of points, before restricting to a curve. -/
theorem selfAdjoint_kernel_square_cross (N : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hA : IsSelfAdjoint A)
    (c d : ℍ → AutomorphicSpace N) (hc : Continuous c) (hd : Continuous d)
    (hci : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hdi : ∀ γ : gamma N,∀ z,d (γ•z)=d z)
    (K : ℍ → ℍ → ℂ) (hK : ∀ x,Continuous (K x))
    (hKi : ∀ x,∀ γ : gamma N,∀ z,K x (γ•z)=K x z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (hsqrep : ∀ v,(A (A v)).val=ᵐ[quotientMeasure N](fun x => inner ℂ (d x) v))
    (hdrep : ∀ x,(d x).val=ᵐ[quotientMeasure N]K x) (x y : ℍ) :
    inner ℂ (c y) (c x)=K x y := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAd : A (c x)=d x := by
    apply ext_inner_right ℂ
    intro v
    apply (hs (c x) v).trans
    have he := continuous_invariant_eq_of_ae N
      (fun z => inner ℂ (c z) (A v)) (fun z => inner ℂ (d z) v)
      (hc.inner continuous_const) (hd.inner continuous_const)
      (fun γ z => by rw [hci]) (fun γ z => by rw [hdi])
      ((hrep (A v)).symm.trans (hsqrep v))
    exact congrFun he x
  have he : (fun z => inner ℂ (c z) (c x))=ᵐ[quotientMeasure N]K x := by
    have hh := (hrep (c x)).symm
    rw [hAd] at hh
    exact hh.trans (hdrep x)
  exact congrFun (continuous_invariant_eq_of_ae N _ _ (hc.inner continuous_const) (hK x)
    (fun γ z => by rw [hci]) (hKi x) he) y

/-- A compact even time test gives a literal physical Abel column. -/
def timeAbelColumn (N : ℕ) [NeZero N] (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) : ℍ → AutomorphicSpace N :=
  oneSidedAbelColumn N (evenCoshLift f) (evenCoshLift_smoothOn f (f.smooth ⊤) he hc)
    R hR (evenCoshLift_support_of_time_support f R hR hs)

/-- The original real even wave packet satisfies its convolution-square
cross-kernel identity globally, including reflection pairs. -/
theorem timeSquare_kernel_cross (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x y : ℍ) :
    inner ℂ (timeAbelColumn N f hc he R hR hs y) (timeAbelColumn N f hc he R hR hs x)=
      radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x y := by
  let F := evenCoshLift f
  have hF : ContDiffOn ℝ ∞ F (Ici 1) := evenCoshLift_smoothOn f (f.smooth ⊤) he hc
  have hsF : Function.support F⊆Iic (Real.cosh R) := evenCoshLift_support_of_time_support f R hR hs
  let g := timeConvolution f f
  have hgc : HasCompactSupport (g : ℝ → ℂ) := timeConvolution_compact f f hc hc
  have hge : Function.Even g := timeConvolution_even f f he he
  have hgr : ∀ t,star (g t)=g t := timeConvolution_real f f hr hr
  have hgs : Function.support g⊆Icc (-(R+R)) (R+R) := timeConvolution_support f f R R hs hs
  let G := evenCoshLift g
  have hG : ContDiffOn ℝ ∞ G (Ici 1) := evenCoshLift_smoothOn g (g.smooth ⊤) hge hgc
  have hsG : Function.support G⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support g (R+R) (add_nonneg hR hR) hgs
  let c := oneSidedAbelColumn N F hF R hR hsF
  let d := oneSidedAbelColumn N G hG (R+R) (add_nonneg hR hR) hsG
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hAc (v : AutomorphicSpace N) : (A v).val=ᵐ[quotientMeasure N]
      (fun z => inner ℂ (c z) v) := by
    simp_rw [c,oneSidedAbelColumn_inner N F hF (evenCoshLift_real f hr) R hR hsF]
    exact evenWavePacket_kernel_coeFn N f (f.smooth ⊤) he hc hr R hR hs v
  have hAd (v : AutomorphicSpace N) : (A (A v)).val=ᵐ[quotientMeasure N]
      (fun z => inner ℂ (d z) v) := by
    simp_rw [d,oneSidedAbelColumn_inner N G hG (evenCoshLift_real g hgr)
      (R+R) (add_nonneg hR hR) hsG]
    exact timeConvolution_wavePacket_kernel N f f hc hc he he hr hr R R hR hR hs hs v
  have hcont := oneSidedAbelKernel_joint_continuous N G hG (R+R) (add_nonneg hR hR) hsG
  exact selfAdjoint_kernel_square_cross N A
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr) c d
    (oneSidedAbelColumn_continuous N F hF R hR hsF)
    (oneSidedAbelColumn_continuous N G hG (R+R) (add_nonneg hR hR) hsG)
    (oneSidedAbelColumn_invariant N F hF R hR hsF)
    (oneSidedAbelColumn_invariant N G hG (R+R) (add_nonneg hR hR) hsG)
    (radialPoincareKernel N (abelProfile G))
    (fun z => Continuous.uncurry_left (f:=radialPoincareKernel N (abelProfile G)) z hcont)
    (fun z γ w => radialPoincareKernel_invariant N (abelProfile G) z w γ) hAc hAd
    (oneSidedAbelColumn_coeFn N G hG (R+R) (add_nonneg hR hR) hsG) x y

#print axioms invariant_ae_eq_volume
#print axioms continuous_invariant_eq_of_ae
#print axioms selfAdjoint_kernel_square_cross
#print axioms timeSquare_kernel_cross

end QuantitativeMaass
