module

public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open QuantitativeArithmeticMaassCuspBand QuantitativeArithmeticMaassCuspMass
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The elementary height integral for genuine hyperbolic area. -/
theorem inverse_square_height_integral (Y H : ℝ) (hY : 0<Y) (hYH : Y≤H) :
    (∫ y in Icc Y H,1/y^2)=1/Y-1/H := by
  have hp (y : ℝ) (hy : y∈uIcc Y H) : 0<y := by
    rw [uIcc_of_le hYH] at hy
    exact hY.trans_le hy.1
  have hi : IntervalIntegrable (fun y : ℝ => 1/y^2) volume Y H := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro y hy
    exact pow_ne_zero _ (hp y hy).ne'
  have hd (y : ℝ) (hy : y∈uIcc Y H) : HasDerivAt (fun y : ℝ => -1/y) (1/y^2) y := by
    have hh := ((hasDerivAt_id y).inv (hp y hy).ne').neg
    have he : (-id⁻¹ : ℝ → ℝ)=(fun y : ℝ => -1/y) := by
      funext y
      simp [div_eq_mul_inv]
    rw [he] at hh
    exact hh.congr_deriv (by dsimp only [id_eq];ring)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_of_le hYH,← integral_Icc_eq_integral_Ioc] at hh
  exact hh.trans (by ring)

/-- A genuine finite cusp rectangle has area at most width divided by its
lower height. No Euclidean/hyperbolic measure identification is assumed. -/
theorem cusp_rectangle_area_bound (W : ℕ) (Y H : ℝ) (hY : 0<Y) :
    (∫ _z in upperRectangle 0 W Y H,(1:ℝ))≤(W:ℝ)/Y := by
  by_cases hYH : Y≤H
  · rw [rectangle_real_integral 0 W Y H hY (fun _ => (1:ℝ)) continuous_const]
    have hex (y : ℝ) : (∫ _x in Icc (0:ℝ) W,1/y^2)=(W:ℝ)*(1/y^2) := by
      rw [integral_const,measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (Nat.cast_nonneg W),sub_zero,smul_eq_mul]
    simp_rw [hex]
    rw [integral_const_mul,inverse_square_height_integral Y H hY hYH]
    have hH : 0<H := hY.trans_le hYH
    have hh : 0≤(W:ℝ)/H := by positivity
    calc
      _ = (W:ℝ)/Y-(W:ℝ)/H := by ring
      _ ≤ _ := sub_le_self _ hh
  · have hempty : upperRectangle 0 W Y H=∅ := by
      ext z
      constructor
      · intro hz
        exact (hYH (hz.2.1.trans hz.2.2)).elim
      · simp
    rw [hempty,setIntegral_empty]
    positivity

/-- Finite actual hyperbolic measure of the full cusp tail, obtained by
exhaustion of finite rectangles. -/
theorem cuspTailSet_volume_bound (W : ℕ) (Y : ℝ) (hY : 0<Y) :
    volume (cuspTailSet W Y)≤ENNReal.ofReal ((W:ℝ)/Y) := by
  have hh := tail_lintegral_le_of_bands W Y (fun _ => (1:ℝ≥0∞)) (ENNReal.ofReal ((W:ℝ)/Y)) (by
    intro H _
    have hi : IntegrableOn (fun _z : ℍ => (1:ℝ)) (upperRectangle 0 W Y H) volume :=
      continuous_const.continuousOn.integrableOn_compact (upperRectangle_compact 0 W Y H hY)
    have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => (zero_le_one : (0:ℝ)≤1)))
    simp only [ENNReal.ofReal_one] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (cusp_rectangle_area_bound W Y H hY))
  simpa only [lintegral_one,Measure.restrict_apply_univ] using hh

#print axioms inverse_square_height_integral
#print axioms cusp_rectangle_area_bound
#print axioms cuspTailSet_volume_bound

end QuantitativeMaass
