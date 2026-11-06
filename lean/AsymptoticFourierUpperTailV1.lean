module

public import AsymptoticFourierNormV1
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFourierNorm

open MeasureTheory Set Filter AsymptoticGammaTail

/-- Doubling height increases the capped weight by at most two. -/
theorem cap_double_le (ε y : ℝ) : min (2*y/ε) 1≤2*min (y/ε) 1 := by
  by_cases hy : y/ε≤1
  · rw [min_eq_left hy]
    convert min_le_left (2*y/ε) 1 using 1; ring
  · rw [min_eq_right (le_of_not_ge hy)]
    exact (min_le_right _ _).trans (by norm_num)

theorem density_half_double_le (m t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : 0≤y) :
    density m t (r/2) ε (2*y)≤2^(m+2*t)*density m t r ε y := by
  have hc : (min (2*y/ε) 1)^(2*t)≤2^(2*t)*(min (y/ε) 1)^(2*t) := by
    simpa only [mul_pow] using pow_le_pow_left₀
      (le_min (div_nonneg (by positivity) hε.le) zero_le_one) (cap_double_le ε y) (2*t)
  have he : -(r/2*(2*y))=-(r*y) := by ring
  unfold density kernel
  rw [mul_pow,he]
  calc
    _ ≤ (2^m*y^m*Real.exp (-(r*y)))*(2^(2*t)*(min (y/ε) 1)^(2*t)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- Rescaling the actual capped radial integral, not an uncapped
approximation, supplies the exponential upper-height estimate. -/
theorem beta_half_le (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    beta m t (r/2) ε≤2^(m+2*t+1)*beta m t r ε := by
  have hi : IntegrableOn (fun y => density m t (r/2) ε (2*y)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (density m t (r/2) ε) 0 (by norm_num : (0:ℝ)<2)).mpr
    rw [mul_zero]
    exact integrable_density m t (half_pos hr) hε
  have he : beta m t (r/2) ε=2*(∫ y in Ioi 0,density m t (r/2) ε (2*y)) := by
    symm
    simpa only [mul_zero,smul_eq_mul,beta] using
      integral_comp_mul_left_Ioi' (density m t (r/2) ε) 0 (by norm_num : (0:ℝ)<2)
  rw [he]
  calc
    _ ≤ 2*(∫ y in Ioi 0,2^(m+2*t)*density m t r ε y) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae hi ((integrable_density m t hr hε).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact density_half_double_le m t r hε hy.le
    _ = _ := by rw [integral_const_mul,pow_succ]; unfold beta; ring

/-- The fraction of the normalized mode above height H. The underlying
positive-height measure makes this definition valid even for H≤0. -/
noncomputable def upperMass (m t : ℕ) (r ε H : ℝ) : ℝ :=
  (∫ y in Ioi H,density m t r ε y ∂(volume.restrict (Ioi 0)))/beta m t r ε

theorem upperMass_nonneg (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) (H : ℝ) :
    0≤upperMass m t r ε H := by
  apply div_nonneg _ (beta_pos m t hr hε).le
  apply integral_nonneg_of_ae
  filter_upwards [(ae_restrict_mem measurableSet_Ioi).filter_mono
    (ae_mono (Measure.restrict_le_self (μ:=volume.restrict (Ioi 0)) (s:=Ioi H)))] with y hy
  exact density_nonneg m t r hε hy.le

theorem upperMass_le_one (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) (H : ℝ) :
    upperMass m t r ε H≤1 := by
  apply (div_le_one (beta_pos m t hr hε)).mpr
  apply setIntegral_le_integral (integrable_density m t hr hε)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact density_nonneg m t r hε hy.le

theorem density_tail_le (m t : ℕ) {r ε H y : ℝ} (hr : 0<r) (hε : 0<ε)
    (hy : 0≤y) (hHy : H≤y) :
    density m t r ε y≤Real.exp (-(r*H/2))*density m t (r/2) ε y := by
  have he : density m t r ε y=Real.exp (-(r*y/2))*density m t (r/2) ε y := by
    unfold density kernel
    rw [show -(r*y)=-(r*y/2)+-(r/2*y) by ring,Real.exp_add]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (density_nonneg m t (r/2) hε hy)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Exponential tail bound from the manuscript, with m=k-2 and r=4πn.
It holds for the capped weighted modes at every positive frequency. -/
theorem upperMass_le_exp (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) (H : ℝ) :
    upperMass m t r ε H≤2^(m+2*t+1)*Real.exp (-(r*H/2)) := by
  apply (div_le_iff₀ (beta_pos m t hr hε)).mpr
  calc
    _ ≤ ∫ y in Ioi H,Real.exp (-(r*H/2))*density m t (r/2) ε y ∂(volume.restrict (Ioi 0)) := by
      apply integral_mono_ae (integrable_density m t hr hε).restrict
        (((integrable_density m t (half_pos hr) hε).const_mul _).restrict)
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        (ae_restrict_mem measurableSet_Ioi).filter_mono
          (ae_mono (Measure.restrict_le_self (μ:=volume.restrict (Ioi 0)) (s:=Ioi H)))] with y hHy hy
      exact density_tail_le m t hr hε hy.le hHy.le
    _ ≤ ∫ y in Ioi 0,Real.exp (-(r*H/2))*density m t (r/2) ε y := by
      apply setIntegral_le_integral ((integrable_density m t (half_pos hr) hε).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (Real.exp_pos _).le (density_nonneg m t (r/2) hε hy.le)
    _ = Real.exp (-(r*H/2))*beta m t (r/2) ε := by rw [integral_const_mul]; rfl
    _ ≤ Real.exp (-(r*H/2))*(2^(m+2*t+1)*beta m t r ε) :=
      mul_le_mul_of_nonneg_left (beta_half_le m t hr hε) (Real.exp_pos _).le
    _ = _ := by ring

#print axioms density_half_double_le
#print axioms beta_half_le
#print axioms upperMass_nonneg
#print axioms upperMass_le_one
#print axioms upperMass_le_exp

end AsymptoticFourierNorm
