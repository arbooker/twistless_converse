module

public import QuantitativeMaassMajorantColumnsV1
public import QuantitativeMaassCylinderColumnLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Normalization acts on the literal cylinder columns by the same scalar. -/
theorem originalMajorantColumn_eq_smul (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) (z : ℍ) :
    let a := t-smoothingWidth (slowScale t) (ε t)
    let b := t+ε t+smoothingWidth (slowScale t) (ε t)
    let f := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t) a b
    let hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
      (radius ε t) (radius_pos ε t) a b
    originalMajorantColumn K hc he ε t z =
      ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹:ℂ) •
        cylinderTimeColumn f (symmetricWindowTimeTest_compact K hc _ a b (radius_pos ε t))
          (symmetricWindowTimeTest_even K he _ a b)
          (supportRadius K hc*radius ε t)
          (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le hs z := by
  intro a b f hs
  apply cylinderAutomorphic.injective
  have hh := cylinderTimeColumn_linear f f (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
    (symmetricWindowTimeTest_compact K hc _ a b (radius_pos ε t))
    (symmetricWindowTimeTest_compact K hc _ a b (radius_pos ε t))
    (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
    (symmetricWindowTimeTest_even K he _ a b) (symmetricWindowTimeTest_even K he _ a b)
    (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    hs hs (originalMajorant_support K hc ε t)
    ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹:ℂ) 0
    (by simp only [zero_smul,add_zero]; rfl) z
  simpa only [originalMajorantColumn,map_smul,zero_smul,add_zero] using hh

/-- The scalar normalization costs at most four in column energy. -/
theorem originalMajorantColumn_norm_sq_le (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) (z : ℍ) :
    let a := t-smoothingWidth (slowScale t) (ε t)
    let b := t+ε t+smoothingWidth (slowScale t) (ε t)
    let f := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t) a b
    let hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
      (radius ε t) (radius_pos ε t) a b
    ‖originalMajorantColumn K hc he ε t z‖^2 ≤
      4*‖cylinderTimeColumn f (symmetricWindowTimeTest_compact K hc _ a b (radius_pos ε t))
          (symmetricWindowTimeTest_even K he _ a b)
          (supportRadius K hc*radius ε t)
          (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le hs z‖^2 := by
  intro a b f hs
  rw [originalMajorantColumn_eq_smul,norm_smul,mul_pow]
  have hd := QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t
  have hi : (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹≤2 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2)
      (le_max_left (1/2:ℝ) (1-(∫ u,|u| * K u)/
        (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t))))
    simpa only [QuantitativeNinaMaass.windowEnergyDenominator,one_div,inv_inv] using hh
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  exact mul_le_mul_of_nonneg_right (by nlinarith [inv_pos.mpr hd]) (sq_nonneg _)

#print axioms originalMajorantColumn_eq_smul
#print axioms originalMajorantColumn_norm_sq_le
end QuantitativeMaass.Scheduled
