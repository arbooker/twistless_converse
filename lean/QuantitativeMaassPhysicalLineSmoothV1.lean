module

public import QuantitativeMaassPhysicalQuadraticMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Iterating the actual mean derivative proves smoothness without extending
any function to the nonphysical side of the radial boundary. -/
theorem physicalQuadraticMean_smooth (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (L : ℝ) :
    ContDiff ℝ ∞ (physicalQuadraticMean F L) := by
  have hn : ∀ n : ℕ,∀ F : ℝ → ℂ,ContDiffOn ℝ ∞ F (Ici 1) →
      ContDiff ℝ n (physicalQuadraticMean F L) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiff_zero.mpr (physicalQuadraticMean_continuous F hF L)
    | succ n ih =>
      intro F hF
      rw [show (↑(n+1):ℕ∞ω)=(n:ℕ∞ω)+1 from by simp,contDiff_succ_iff_deriv]
      refine ⟨fun v => (physicalQuadraticMean_hasDerivAt F hF L v).differentiableAt,by simp,?_⟩
      have he : deriv (physicalQuadraticMean F L)=
          fun v => v • physicalQuadraticMean (derivWithin F (Ici 1)) L v :=
        funext (fun v => (physicalQuadraticMean_hasDerivAt F hF L v).deriv)
      rw [he]
      exact contDiff_id.smul (ih _ (hF.derivWithin (uniqueDiffOn_Ici (1:ℝ)) (by simp)))
  exact contDiff_infty.mpr (fun n => hn n F hF)

/-- Exact square-coordinate representation of the physical horizontal Abel
profile. The ordinary derivative at the endpoint itself is irrelevant. -/
theorem abelProfile_horizontal_mean (F : ℝ → ℂ)
    (B : ℝ) (hB : 1≤B) (hs : Function.support F⊆Iic B) (v : ℝ) :
    parabolicLineProfile (abelProfile F) 1 v=
      -(Real.sqrt 2/Real.pi:ℂ)*physicalQuadraticMean (derivWithin F (Ici 1)) (B+1) v := by
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  unfold parabolicLineProfile abelProfile physicalQuadraticMean
  simp only [one_pow,mul_one]
  rw [abelIntegral_physical_interval _ B hB hd _ (by nlinarith [sq_nonneg v]),
    integral_Icc_eq_integral_Ioc]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs0
  have hq : 1<1+v^2/2+s^2 := by nlinarith [sq_nonneg v,sq_pos_of_pos hs0.1]
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hq)]

/-- The actual horizontal Abel profile is globally smooth for every height,
even though its original radial test is only smooth on the physical half-line. -/
theorem abelProfile_horizontal_smooth (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (y : ℝ) :
    ContDiff ℝ ∞ (parabolicLineProfile (abelProfile F) y) := by
  have he : parabolicLineProfile (abelProfile F) y=fun v =>
      -(Real.sqrt 2/Real.pi:ℂ)*physicalQuadraticMean (derivWithin F (Ici 1)) (B+1) (v/y) := by
    funext v
    rw [parabolicLineProfile_height_scale,abelProfile_horizontal_mean F B hB hs]
  rw [he]
  exact contDiff_const.mul ((physicalQuadraticMean_smooth _
    (hF.derivWithin (uniqueDiffOn_Ici (1:ℝ)) (by simp)) (B+1)).comp (contDiff_id.div_const y))

#print axioms physicalQuadraticMean_smooth
#print axioms abelProfile_horizontal_mean
#print axioms abelProfile_horizontal_smooth

end QuantitativeMaass
