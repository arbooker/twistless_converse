module

public import QuantitativeNinaMaassWeakFourierV1
public import QuantitativeArithmeticMaassCuspLocalizationV1
public import QuantitativeMaassCuspPoincareV1
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix QuantitativeMaass
open QuantitativeArithmeticMaassCuspBand QuantitativeArithmeticMaassCuspMass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups

/-!
Actual Fourier profiles have finite hyperbolic energy on every high cusp
tail. The bound uses the proved physical cusp restriction, finite-rectangle
Fubini and integral Cauchy--Schwarz. Square-integrability of a Fourier profile
is a conclusion; it is not supplied to the eigenform construction.
-/

namespace QuantitativeNinaMaass

theorem unitLineFourierCoeff_norm_sq_le (F : ℝ → ℂ) (hF : Continuous F) (n : ℤ) :
    ‖unitLineFourierCoeff F n‖ ^ 2 ≤ ∫ x in Icc (0 : ℝ) 1, ‖F x‖ ^ 2 := by
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (f := fun x => fourier (-n) (x : AddCircle (1 : ℝ)) * F x)
  have he (x : ℝ) : ‖fourier (-n) (x : AddCircle (1 : ℝ)) * F x‖ = ‖F x‖ := by
    rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  simp_rw [he] at hnorm
  have hsq := interval_integral_sq_le_length (fun x => ‖F x‖) hF.norm 1 zero_lt_one
  rw [one_mul] at hsq
  change ‖unitLineFourierCoeff F n‖ ≤ ∫ x in (0 : ℝ)..1, ‖F x‖ at hnorm
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hsq hnorm
  nlinarith [norm_nonneg (unitLineFourierCoeff F n)]

theorem cartesianFourier_band_energy_le (F : ℍ → ℂ) (hF : Continuous F)
    (n : ℤ) (a b : ℝ) (ha : 0 < a) :
    (∫ y in Icc a b, ‖cartesianFourier F n y‖ ^ 2 / y ^ 2) ≤
      ∫ z in upperRectangle 0 1 a b, ‖F z‖ ^ 2 := by
  rw [rectangle_real_integral 0 1 a b ha (fun z => ‖F z‖ ^ 2) (hF.norm.pow 2)]
  have hc : ContinuousOn (fun y => ‖cartesianFourier F n y‖ ^ 2 / y ^ 2) (Ioi 0) :=
    ((cartesianFourier_continuousOn F hF n).norm.pow 2).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt hy))
  apply setIntegral_mono_on
    ((hc.mono (fun y hy => ha.trans_le hy.1)).integrableOn_compact isCompact_Icc)
    (rectangle_iterated_integrable 0 1 a b ha _ (hF.norm.pow 2)) measurableSet_Icc
  intro y hy
  have hpos := ha.trans_le hy.1
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (unitLineFourierCoeff_norm_sq_le (fun x => F (cartesianLift (x, y)))
      (hF.comp (cartesianLift_horizontal_continuous y hpos)) n) (sq_nonneg y)

theorem representative_identity_tail_integrable (N : ℕ) (a : ℝ) (ha : 2 ≤ a)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    IntegrableOn (fun z => ‖f.val z‖ ^ 2) (cuspTailSet 1 a) := by
  have h := (representative_tail_memLp N 1 (1 : SL(2, ℤ)) a ha f).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [IntegrableOn, cuspAction, map_one, one_smul] using h

/-- Every literal horocycle Fourier integral of an actual continuous
quotient-L2 representative is square-integrable with weight y^-2 on the
high cusp tail. This does not require an eigenvalue or cuspidality premise. -/
theorem cartesianFourier_hyperbolic_integrable (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (n : ℤ) (a : ℝ) (ha : 2 ≤ a) :
    IntegrableOn (fun y => ‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2) (Ioi a) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  let C := ∫ z in cuspTailSet 1 a, ‖f.val z‖ ^ 2
  have htail := representative_identity_tail_integrable N a ha f
  have hc : ContinuousOn (fun y => ‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2) (Ioi 0) :=
    ((cartesianFourier_continuousOn f.val hf n).norm.pow 2).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt hy))
  have hi (b : ℝ) : IntegrableOn (fun y => ‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2) (Icc a b) :=
    (hc.mono (fun y hy => ha0.trans_le hy.1)).integrableOn_compact isCompact_Icc
  have hb (b : ℝ) : (∫ y in Icc a b, ‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2) ≤ C := by
    apply (cartesianFourier_band_energy_le f.val hf n a b ha0).trans
    apply setIntegral_mono_set htail
    · exact Eventually.of_forall (fun _ => sq_nonneg _)
    · exact Eventually.of_forall (fun z hz =>
        ⟨by simpa only [Nat.cast_one] using hz.1, hz.2.1⟩)
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded C a
    (b := fun b : ℝ => b) (l := atTop)
  · intro b
    exact (hi b).mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop a] with b hab
    have he (y : ℝ) : ‖‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2‖ =
        ‖cartesianFourier f.val n y‖ ^ 2 / y ^ 2 :=
      Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg y))
    simp_rw [he]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact hb b

#print axioms unitLineFourierCoeff_norm_sq_le
#print axioms cartesianFourier_band_energy_le
#print axioms representative_identity_tail_integrable
#print axioms cartesianFourier_hyperbolic_integrable

end QuantitativeNinaMaass
