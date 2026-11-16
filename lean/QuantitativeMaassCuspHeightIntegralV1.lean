module

public import QuantitativeMaassCuspWindowBoundV1
public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open QuantitativeSpectralObservability QuantitativeArithmeticMaassCuspMass
open QuantitativeArithmeticMaassCuspBand
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Explicit primitive for the cusp weight that arises after hyperbolic
volume cancels one and a half powers of height. -/
theorem cusp_inverse_sqrt_integral (H : ℝ) (hH : (1:ℝ)/4≤H) :
    (∫ y in Icc ((1:ℝ)/4) H,1/Real.sqrt y)=2*Real.sqrt H-1 := by
  have hp (y : ℝ) (hy : y∈Icc ((1:ℝ)/4) H) : 0<y := by linarith [hy.1]
  have hc : ContinuousOn (fun y : ℝ => 1/Real.sqrt y) (Icc ((1:ℝ)/4) H) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun y hy => (Real.sqrt_pos.mpr (hp y hy)).ne')
  have hi : IntervalIntegrable (fun y : ℝ => 1/Real.sqrt y) volume ((1:ℝ)/4) H :=
    hc.intervalIntegrable_of_Icc hH
  have hd (y : ℝ) (hy : y∈uIcc ((1:ℝ)/4) H) :
      HasDerivAt (fun x : ℝ => 2*Real.sqrt x) (1/Real.sqrt y) y := by
    rw [uIcc_of_le hH] at hy
    have hh := (Real.hasDerivAt_sqrt (hp y hy).ne').const_mul 2
    convert hh using 1
    field_simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_of_le hH,← integral_Icc_eq_integral_Ioc] at hh
  have hs : Real.sqrt ((1:ℝ)/4)=1/2 := by norm_num
  simpa only [hs,show (2:ℝ)*(1/2)=1 by norm_num] using hh

/-- The full height^(3/2) kernel majorant integrates to O(sqrt(H)) on the
actual standard cusp box, with an absolute explicit constant. -/
theorem cusp_height_majorant_integral (H : ℝ) (hH : (1:ℝ)/4≤H) :
    (∫ z in wideBox H,(1+z.im)*Real.sqrt z.im)≤30*Real.sqrt H := by
  have he : wideBox H=upperRectangle (-1) 2 ((1:ℝ)/4) H := by
    ext z
    simp only [wideBox,upperRectangle,mem_ofPred_eq,mem_prod,mem_Icc]
    tauto
  rw [he,rectangle_real_integral (-1) 2 ((1:ℝ)/4) H (by norm_num)
    (fun z => (1+z.im)*Real.sqrt z.im) (by fun_prop)]
  have hp (y : ℝ) (hy : y∈Icc ((1:ℝ)/4) H) : 0<y := by linarith [hy.1]
  have hi := rectangle_iterated_integrable (-1) 2 ((1:ℝ)/4) H (by norm_num)
    (fun z => (1+z.im)*Real.sqrt z.im) (by fun_prop)
  have hj : IntegrableOn (fun y : ℝ => 15/Real.sqrt y) (Icc ((1:ℝ)/4) H) :=
    (continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun y hy => (Real.sqrt_pos.mpr (hp y hy)).ne')).integrableOn_compact isCompact_Icc
  have hb : (∫ y in Icc ((1:ℝ)/4) H,∫ x in Icc (-1:ℝ) 2,
      ((1+(cartesianLift (x,y)).im)*Real.sqrt (cartesianLift (x,y)).im)/y^2)≤
      ∫ y in Icc ((1:ℝ)/4) H,15/Real.sqrt y := by
    apply setIntegral_mono_on hi hj measurableSet_Icc
    intro y hy
    have heq : (∫ x in Icc (-1:ℝ) 2,
        ((1+(cartesianLift (x,y)).im)*Real.sqrt (cartesianLift (x,y)).im)/y^2)=
        3*(1+y)*Real.sqrt y/y^2 := by
      have hf : (fun x : ℝ => ((1+(cartesianLift (x,y)).im)*Real.sqrt (cartesianLift (x,y)).im)/y^2)=
          fun _ => (1+y)*Real.sqrt y/y^2 := by
        funext x
        rw [cartesianLift_positive (x,y) (hp y hy)]
        rfl
      rw [hf,integral_const]
      norm_num [Real.volume_Icc,smul_eq_mul]
      ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos (hp y hy)) (Real.sqrt_pos.mpr (hp y hy))).mpr
    calc
      _ = 3*(1+y)*y := by rw [mul_assoc,← sq,Real.sq_sqrt (hp y hy).le]
      _ ≤ _ := by nlinarith [hy.1]
  apply hb.trans
  have heq : (∫ y in Icc ((1:ℝ)/4) H,15/Real.sqrt y)=15*(2*Real.sqrt H-1) := by
    simp_rw [show ∀ y : ℝ,15/Real.sqrt y=15*(1/Real.sqrt y) from fun y => by ring]
    rw [integral_const_mul,cusp_inverse_sqrt_integral H hH]
  rw [heq]
  linarith

#print axioms cusp_inverse_sqrt_integral
#print axioms cusp_height_majorant_integral

end QuantitativeMaass
