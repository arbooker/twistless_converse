module

public import QuantitativeMaassCoshLiftSecondBoundV1
public import QuantitativeMaassModulatedDerivativeBoundsV1
public import QuantitativeMaassPhysicalAbelSmallVariationV1
public import QuantitativeMaassWindowCenteredKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The entire inverse-square inner radius has a uniform explicit variation
bound. Its spectral growth is cancelled by the shrinking integration interval. -/
theorem windowTimeSquareProfile_initial_variation (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B D : ℝ,0<B ∧ 0<D ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t →
      (∫ r in (0:ℝ)..(1/t)^2,‖deriv (fun r => windowTimeSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) (Real.cosh r)) r‖)≤D*R*ε^2*(Real.cosh (B*R)+1)^2 := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowTimeSquare_four_derivative_bounds K he hc
  let G := Real.sqrt 2/Real.pi
  have hG : 0<G := by dsimp only [G];positivity
  refine ⟨B,16*G*C*Real.cosh 1,hB,by positivity,?_⟩
  intro R hR ε hε hε1 t ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  let w := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  let f := timeConvolution w w
  let M := C*R*ε^2*(t+1)^4
  have hM : 0≤M := by dsimp only [M];positivity
  have hwe : Function.Even w := symmetricWindowTimeTest_even K he R (t-ε) (t+ε)
  have hwc : HasCompactSupport (w : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R (t-ε) (t+ε) hRp
  have hfe : Function.Even f := timeConvolution_even w w hwe hwe
  have hfc : HasCompactSupport (f : ℝ → ℂ) := timeConvolution_compact w w hwc hwc
  obtain ⟨hfs,hfd⟩ := hbounds R hR ε hε hε1 t ht
  change Function.support (f : ℝ → ℂ)⊆Icc (-(B*R)) (B*R) at hfs
  change ∀ n : ℕ,n≤4 → ∀ u,‖iteratedDeriv n (f : ℝ → ℂ) u‖≤M at hfd
  have hb2 (u : ℝ) : ‖deriv (deriv (f : ℝ → ℂ)) u‖≤M := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfd 2 (by omega) u
  have hb4 (u : ℝ) : ‖deriv (deriv (deriv (deriv (f : ℝ → ℂ)))) u‖≤M := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfd 4 le_rfl u
  have hb := evenCoshLift_second_bound_physical f (f.smooth ⊤) hfe hfc (B*R) M M
    (by positivity) hfs hM hM hb2 hb4
  have hh := abelProfile_initial_radial_variation (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) hfe hfc) (Real.cosh (B*R))
    (M+M*Real.cosh (B*R)) ((1/t)^2) (Real.one_le_cosh _) (by positivity) (sq_nonneg _)
    (evenCoshLift_support_of_time_support f (B*R) (by positivity) hfs) hb
  have hti : 0<1/t := one_div_pos.mpr ht0
  have hti1 : 1/t≤1 := (div_le_one ht0).mpr ht
  have hδ1 : (1/t)^2≤1 := by nlinarith
  have hcosh : Real.cosh ((1/t)^2)≤Real.cosh 1 :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg (sq_nonneg (1/t)),abs_one] using hδ1)
  have hsmall : Real.cosh ((1/t)^2)-1≤Real.cosh 1*((1/t)^2)^2 := by
    have h := cosh_sub_one_le_quadratic ((1/t)^2) (sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hcosh (sq_nonneg ((1/t)^2))
    nlinarith [Real.cosh_pos 1,pow_nonneg hti.le 4]
  have hfreq : (t+1)^4*((1/t)^2)^2≤16 := by
    have hpow := pow_le_pow_left₀ (by positivity : 0≤t+1) (by linarith : t+1≤2*t) 4
    have hh := mul_le_mul_of_nonneg_right hpow (pow_nonneg hti.le 4)
    have hid : (2*t)^4*(1/t)^4=(16:ℝ) := by field_simp;ring
    rw [hid] at hh
    convert hh using 1
    ring
  change (∫ r in (0:ℝ)..(1/t)^2,‖deriv (fun r => abelProfile (evenCoshLift f) (Real.cosh r)) r‖)≤_
  apply hh.trans
  have hcoeff : 0≤G*(M+M*Real.cosh (B*R))*(Real.cosh (B*R)+1) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hsmall hcoeff
  have hstep2 := mul_le_mul_of_nonneg_left hfreq
    (show 0≤G*C*R*ε^2*(Real.cosh (B*R)+1)^2*Real.cosh 1 by positivity)
  dsimp only [M,G] at hstep hstep2 ⊢
  nlinarith

#print axioms windowTimeSquareProfile_initial_variation

end QuantitativeMaass
