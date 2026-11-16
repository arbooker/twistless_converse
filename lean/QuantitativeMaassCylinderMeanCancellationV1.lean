module

public import QuantitativeMaassColumnMeanFubiniV1
public import QuantitativeMaassCylinderMeanHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The literal averaged kernel annihilates every nonzero-mode cylinder vector. -/
theorem cylinderRadialMean_pairing_zero (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (z : ℍ) (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    (∫ w,cylinderRadialMean g z w*v w ∂quotientMeasure 0)=0 := by
  let a := Real.exp (Real.log z.im-R)
  let b := Real.exp (Real.log z.im+R)
  let h := cylinderRadialMeanHeight g z a
  have hh : Continuous h := cylinderRadialMeanHeight_continuous g hg R hR hs z a (Real.exp_pos _)
  calc
    _ = ∫ w,(upperRectangle 0 1 a b).indicator (fun w => h w.im*v w) w ∂quotientMeasure 0 := by
      apply integral_congr_ae
      filter_upwards [cylinderRadialMean_height_indicator g R hR hs z] with w hw
      rw [hw]
      change (upperRectangle 0 1 a b).indicator (fun w => h w.im) w*v w=
        (upperRectangle 0 1 a b).indicator (fun w => h w.im*v w) w
      classical
      by_cases hK : w∈upperRectangle 0 1 a b
      · simp only [Set.indicator_of_mem hK]
      · simp only [Set.indicator_of_notMem hK,zero_mul]
    _ = ∫ w in upperRectangle 0 1 a b,h w.im*v w ∂quotientMeasure 0 :=
      integral_indicator (upperRectangle_measurable 0 1 a b)
    _ = ∫ w in upperRectangle 0 1 a b,h w.im*v w := by
      rw [cylinder_rectangle_measure a b (Real.exp_pos _)]
    _ = 0 := by
      simpa only [star_star] using
        cylinderNonzeroModes_height_pairing_zero a b (Real.exp_pos _) (fun y => star (h y)) hh.star v hv

/-- The Hilbert-valued period mean of the actual Abel columns vanishes
against the whole closed nonzero-mode subspace. -/
theorem cylinderAbelColumn_mean_orthogonal (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (z : ℍ) (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    inner ℂ (∫ x in Icc (0:ℝ) 1,cylinderAbelColumn F hF R hR hs (x+ᵥz)) v=0 := by
  let c := fun x : ℝ => cylinderAbelColumn F hF R hR hs (x+ᵥz)
  let k := fun (x : ℝ) (w : ℍ) => radialPoincareKernel 0 (abelProfile F) (x+ᵥz) w
  have hc : Continuous c := (cylinderAbelColumn_continuous F hF R hR hs).comp (cylinder_vadd_continuous z)
  have hk : Measurable (Function.uncurry k) :=
    ((oneSidedAbelKernel_joint_continuous 0 F hF R hR hs).comp
      (((cylinder_vadd_continuous z).comp continuous_fst).prodMk continuous_snd)).measurable
  have hi := continuous_column_pairing_integrable k hk c hc
    (fun x => cylinderAbelColumn_coeFn F hF R hR hs (x+ᵥz)) v
  change inner ℂ (∫ x in Icc (0:ℝ) 1,c x) v=0
  rw [←inner_conj_symm (∫ x in Icc (0:ℝ) 1,c x) v,
    ←integral_inner hc.integrableOn_Icc v,←integral_conj]
  simp only [inner_conj_symm]
  simp_rw [show ∀ x,inner ℂ (c x) v=∫ w,k x w*v w ∂quotientMeasure 0 from
    fun x => cylinderAbelColumn_inner F hF hr R hR hs (x+ᵥz) v]
  rw [integral_integral_swap hi]
  simp_rw [integral_mul_const]
  exact cylinderRadialMean_pairing_zero (abelProfile F)
    (abelProfile_continuousOn_physical F hF (Real.cosh R) (Real.one_le_cosh R) hs) R hR (abelProfile_support F _ hs) z v hv

#print axioms cylinderRadialMean_pairing_zero
#print axioms cylinderAbelColumn_mean_orthogonal

end QuantitativeMaass
