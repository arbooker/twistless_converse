module

public import QuantitativeMaassAllLevelRadialOperatorV1
public import QuantitativeMaassCappedConjugationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem cappedHeightWeight_cylinder_invariant (ε : ℝ) (t : ℕ) (γ : gamma 0) (z : ℍ) :
    cappedHeightWeight ε t (γ.val • z)=cappedHeightWeight ε t z := by
  obtain ⟨n,hn⟩ := gamma_zero_translation γ
  simp only [cappedHeightWeight,hn,AsymptoticCompactTranslation.label_im]

/-- Literal cylinder kernels cannot couple logarithmic weight bands farther
apart than their geometric propagation radius permits. -/
theorem cylinder_radial_kernel_band_zero (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (n m : ℤ) (x y : ℍ)
    (hx : x∈LogBands.region (fun z => Real.log (cappedHeightWeight ε t z)) n)
    (hy : y∈LogBands.region (fun z => Real.log (cappedHeightWeight ε t z)) m)
    (hsep : (t:ℝ)*R+1≤|(n:ℝ)-(m:ℝ)|) :
    radialPoincareKernel 0 g x y=0 := by
  unfold radialPoincareKernel poincareSum
  suffices hzero : ∀ γ : gamma 0, upperFunction (radialFunction g x) (γ • y)=0 by
    simp only [hzero,tsum_zero]
  intro γ
  rw [radialFunction_upper]
  by_contra hn
  have hd := Real.cosh_le_cosh.mp (hs hn)
  rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hd
  have hy' : (m:ℝ)≤Real.log (cappedHeightWeight ε t (γ.val • y)) ∧
      Real.log (cappedHeightWeight ε t (γ.val • y))<(m:ℝ)+1 := by
    rw [cappedHeightWeight_cylinder_invariant]
    exact hy
  exact (not_lt_of_ge hsep) (cappedHeightWeight_band_separation hε t x (γ.val • y) n m R
    (by change dist (γ.val • y) x≤R at hd; rwa [dist_comm] at hd) hx hy')

/-- Band propagation for the actual Schur integral operator, with no
spectral-action premise. -/
theorem cylinder_radial_band_propagation (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    {ε : ℝ} (hε : 0<ε) (t J : ℕ) (hJ : (t:ℝ)*R+1≤(J:ℝ)) :
    LogBands.HasBandPropagation (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
      (radialKernelData 0 g hg R hR hs).operator J := by
  intro n m hnm f
  let l : ℍ → ℝ := fun z => Real.log (cappedHeightWeight ε t z)
  let hl := cappedHeightWeight_log_measurable ε t
  let D := radialKernelData 0 g hg R hR hs
  let v := LogBands.projection (quotientMeasure 0) l hl m f
  have hsep : (t:ℝ)*R+1≤|(n:ℝ)-(m:ℝ)| := by
    have hh : (J:ℝ) < |(n:ℝ)-(m:ℝ)| := by exact_mod_cast hnm
    exact hJ.trans hh.le
  apply Lp.ext
  filter_upwards [LogBands.projection_coeFn (quotientMeasure 0) l hl n (D.operator v),
    D.operator_coeFn v,Lp.coeFn_zero ℂ 2 (quotientMeasure 0)] with x hx hD h0
  rw [hx,h0]
  by_cases hxn : x∈LogBands.region l n
  · rw [Set.indicator_of_mem hxn,hD]
    apply integral_eq_zero_of_ae
    filter_upwards [LogBands.projection_coeFn (quotientMeasure 0) l hl m f] with y hy
    change radialPoincareKernel 0 g x y*v y=0
    change v y=(LogBands.region l m).indicator f y at hy
    rw [hy]
    by_cases hym : y∈LogBands.region l m
    · rw [cylinder_radial_kernel_band_zero g R hR hs hε t n m x y hxn hym hsep,zero_mul]
    · rw [Set.indicator_of_notMem hym,mul_zero]
  · rw [Set.indicator_of_notMem hxn]
    rfl

#print axioms cappedHeightWeight_cylinder_invariant
#print axioms cylinder_radial_kernel_band_zero
#print axioms cylinder_radial_band_propagation

end QuantitativeMaass
