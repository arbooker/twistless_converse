module
public import AsymptoticL2MultiplierV1
public import QuantitativeMaassCuspConstantOperatorV1
public import QuantitativeMaassCuspRectangleIntegralV1
set_option autoImplicit false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped MatrixGroups
namespace QuantitativeArithmeticMaassCuspMass
open QuantitativeMaass

/-- The actual restriction norm is the literal mass in the cusp chart. -/
theorem restriction_norm_sq (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ)
    (hK : IsCompact K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖cuspRestriction N s K hK
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)‖^2 =
      ∫ z in K, ‖f.val (cuspAction s z)‖^2 := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [cuspRestriction_representative_ae N s K hK f] with z hz
  rw [hz]

/-- The mean term has exactly the norm of the already constructed bounded
constant-term operator; no new averaging operator is introduced. -/
theorem constant_norm_sq (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ))
    (a b : ℝ) (ha : 0 < a)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    ‖cuspConstantLocal N s a b ha
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)‖^2 =
      ∫ y, ‖cuspConstant N s f.val y‖^2 ∂heightMeasure (upperRectangle 0 N a b) := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [cuspConstantLocal_representative_ae N hN s a b ha f hf] with y hy
  rw [hy]

/-- Real-valued Fubini on the genuine hyperbolic rectangle. -/
theorem rectangle_real_integral (l r a b : ℝ) (ha : 0 < a)
    (F : ℍ → ℝ) (hF : Continuous F) :
    (∫ z in upperRectangle l r a b, F z) =
      ∫ y in Icc a b, ∫ x in Icc l r, F (cartesianLift (x,y))/y^2 := by
  have h := integral_upperRectangle_iterated l r a b ha
    (fun z => (F z : ℂ)) (Complex.continuous_ofReal.comp hF)
  simp_rw [← Complex.ofReal_pow, ← Complex.ofReal_div, integral_complex_ofReal] at h
  exact_mod_cast h

/-- Real height marginal, with its exact hyperbolic density. -/
theorem height_real_integral (l r a b : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ y, g y ∂heightMeasure (upperRectangle l r a b)) =
      ∫ y in Icc a b, (volume (Icc l r)).toReal * (g y/y^2) := by
  have h := heightMeasure_rectangle_integral l r a b ha
    (fun y => (g y : ℂ)) (Complex.continuous_ofReal.comp hg)
  simp_rw [Complex.real_smul, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_mul, integral_complex_ofReal] at h
  exact_mod_cast h

#print axioms restriction_norm_sq
#print axioms constant_norm_sq
#print axioms rectangle_real_integral
#print axioms height_real_integral
end QuantitativeArithmeticMaassCuspMass
