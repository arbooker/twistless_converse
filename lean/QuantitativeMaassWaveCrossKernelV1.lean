module

public import QuantitativeMaassTimeTranslatePacketV1
public import QuantitativeMaassTranslatedCorrespondenceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace SchwartzMap

namespace QuantitativeMaass

/-- A bounded self-adjoint insertion between two genuine smoothing operators
has its actual continuous cross kernel at every pair of centres. -/
theorem selfAdjoint_kernel_insert_cross (N : ℕ)
    (A U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : IsSelfAdjoint A) (hU : IsSelfAdjoint U)
    (c d : ℍ → AutomorphicSpace N) (hc : Continuous c) (hd : Continuous d)
    (hci : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hdi : ∀ γ : gamma N,∀ z,d (γ•z)=d z)
    (K : ℍ → ℍ → ℂ) (hK : ∀ x,Continuous (K x))
    (hKi : ∀ x,∀ γ : gamma N,∀ z,K x (γ•z)=K x z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (hsqrep : ∀ v,(A (U (A v))).val=ᵐ[quotientMeasure N](fun x => inner ℂ (d x) v))
    (hdrep : ∀ x,(d x).val=ᵐ[quotientMeasure N]K x) (x y : ℍ) :
    inner ℂ (U (c y)) (c x)=K x y := by
  have ha := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hu := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hU
  have hAd : A (U (c x))=d x := by
    apply ext_inner_right ℂ
    intro v
    apply (ha (U (c x)) v).trans
    apply (hu (c x) (A v)).trans
    have he := continuous_invariant_eq_of_ae N
      (fun z => inner ℂ (c z) (U (A v))) (fun z => inner ℂ (d z) v)
      (hc.inner continuous_const) (hd.inner continuous_const)
      (fun γ z => by rw [hci]) (fun γ z => by rw [hdi])
      ((hrep (U (A v))).symm.trans (hsqrep v))
    exact congrFun he x
  have he : (fun z => inner ℂ (c z) (U (c x)))=ᵐ[quotientMeasure N]K x := by
    have hh := (hrep (U (c x))).symm
    rw [hAd] at hh
    exact hh.trans (hdrep x)
  apply (hu (c y) (c x)).trans
  exact congrFun (continuous_invariant_eq_of_ae N _ _ (hc.inner continuous_const) (hK x)
    (fun γ z => by rw [hci]) (hKi x) he) y

/-- The actual wave inserted between original time columns has the translated
convolution-square Abel kernel, globally in both centres. -/
theorem timeSquare_wave_kernel_cross (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (s : ℝ) (x y : ℍ) :
    inner ℂ (Wave.shiftedQuotientWave N s (timeAbelColumn N f hc he R hR hs y))
      (timeAbelColumn N f hc he R hR hs x)=
      radialPoincareKernel N (abelProfile (evenCoshLift (evenTimeTranslate s (timeConvolution f f)))) x y := by
  let g := evenTimeTranslate s (timeConvolution f f)
  have hg : ContDiff ℝ ∞ g := evenTimeTranslate_smooth s _ ((timeConvolution f f).smooth ⊤)
  have hgc : HasCompactSupport g := evenTimeTranslate_compact s _ (timeConvolution_compact f f hc hc)
  have hge : Function.Even g := evenTimeTranslate_even s _ (timeConvolution_even f f he he)
  have hgr : ∀ t,star (g t)=g t := evenTimeTranslate_real s _ (timeConvolution_real f f hr hr)
  let S := R+R+|s|
  have hS : 0≤S := by dsimp only [S];positivity
  have hgs : Function.support g⊆Icc (-S) S :=
    evenTimeTranslate_support s (R+R) _ (timeConvolution_support f f R R hs hs)
  let G := evenCoshLift g
  have hG : ContDiffOn ℝ ∞ G (Ici 1) := evenCoshLift_smoothOn g hg hge hgc
  have hsG : Function.support G⊆Iic (Real.cosh S) := evenCoshLift_support_of_time_support g S hS hgs
  let c := timeAbelColumn N f hc he R hR hs
  let d := oneSidedAbelColumn N G hG S hS hsG
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  let U := Wave.shiftedQuotientWave N s
  have hAc (v : AutomorphicSpace N) : (A v).val=ᵐ[quotientMeasure N](fun z => inner ℂ (c z) v) :=
    timeAbelColumn_packet_coeFn N f hc he hr R hR hs v
  have hAd (v : AutomorphicSpace N) : (A (U (A v))).val=ᵐ[quotientMeasure N]
      (fun z => inner ℂ (d z) v) := by
    simp_rw [d,oneSidedAbelColumn_inner N G hG (evenCoshLift_real g hgr) S hS hsG]
    have hh := evenWavePacket_kernel_coeFn N g hg hge hgc hgr S hS hgs v
    rw [evenTimeTranslate_timeSquare_wavePacket N f hc he s] at hh
    exact hh
  have hcont := oneSidedAbelKernel_joint_continuous N G hG S hS hsG
  exact selfAdjoint_kernel_insert_cross N A U
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr) (Wave.shiftedQuotientWave_isSelfAdjoint N s)
    c d (oneSidedAbelColumn_continuous N _ _ _ _ _)
    (oneSidedAbelColumn_continuous N G hG S hS hsG)
    (oneSidedAbelColumn_invariant N _ _ _ _ _) (oneSidedAbelColumn_invariant N G hG S hS hsG)
    (radialPoincareKernel N (abelProfile G))
    (fun z => Continuous.uncurry_left (f:=radialPoincareKernel N (abelProfile G)) z hcont)
    (fun z γ w => radialPoincareKernel_invariant N (abelProfile G) z w γ) hAc hAd
    (oneSidedAbelColumn_coeFn N G hG S hS hsG) x y

/-- Every actual Hecke power with one actual wave has its standard finite
branch expansion in the translated time-square kernel. -/
theorem timeSquare_wave_hecke_power_kernel (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (s : ℝ)
    (n : ℕ) (x y : ℍ) :
    inner ℂ (Wave.shiftedQuotientWave N s
      (((HeckeL2.operator N p hN hpN a b hab)^n) (timeAbelColumn N f hc he R hR hs x)))
      (timeAbelColumn N f hc he R hR hs y)=
      heckeBranchIterate 1 p n (fun z => radialPoincareKernel N
        (abelProfile (evenCoshLift (evenTimeTranslate s (timeConvolution f f)))) y z) x := by
  let T := HeckeL2.operator N p hN hpN a b hab
  let W := Wave.shiftedQuotientWave N s
  let c := timeAbelColumn N f hc he R hR hs
  let α : ℂ := (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)
  have hcol (z : ℍ) : T (c z)=α • ∑ j : Option (ZMod p),c (cuspBranchGL 1 p j • z) :=
    timeAbelColumn_hecke_standard N p hN hpN hNp a b hab f hc he hr R hR hs z
  change inner ℂ (W ((T^n) (c x))) (c y)=_
  induction n generalizing x with
  | zero =>
    simpa only [pow_zero,one_apply_eq_self,heckeBranchIterate] using
      timeSquare_wave_kernel_cross N f hc he hr R hR hs s y x
  | succ n ih =>
    rw [pow_succ]
    change inner ℂ (W ((T^n) (T (c x)))) (c y)=_
    rw [hcol,map_smul,map_sum,map_smul,map_sum]
    rw [inner_smul_left (∑ j : Option (ZMod p),W ((T^n) (c (cuspBranchGL 1 p j • x)))) (c y) α,sum_inner]
    simp_rw [ih]
    simp only [heckeBranchIterate,normalizedCuspHecke,cuspHeckeSum,α,Complex.real_smul,Complex.conj_ofReal]

#print axioms selfAdjoint_kernel_insert_cross
#print axioms timeSquare_wave_kernel_cross
#print axioms timeSquare_wave_hecke_power_kernel

end QuantitativeMaass
