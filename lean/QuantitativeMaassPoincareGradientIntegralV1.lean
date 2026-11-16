module

public import QuantitativeMaassPoincareGradientBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass
open MaassDifferential

/-- Integrating the compact-overlap estimate controls the periodized gradient
in the actual quotient measure. -/
theorem compact_poincare_gradient_lintegral_bound (N : ℕ) (K : Set ℍ) (hK : IsCompact K) :
    ∃ M : ℕ,∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      (∫⁻ z,ENNReal.ofReal ((upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re) ∂quotientMeasure N)≤
        (M:ℝ≥0∞)*∫⁻ z : ℍ,ENNReal.ofReal ((upperEnergy u.toFun u.toFun z).re) := by
  classical
  obtain ⟨M,hM⟩ := compact_poincare_gradient_square_bound N K hK
  refine ⟨M,?_⟩
  intro u hu
  have hpoint (z : ℍ) :
      ENNReal.ofReal ((upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re)≤
        (M:ℝ≥0∞)*∑' g : gamma N,ENNReal.ofReal ((upperEnergy u.toFun u.toFun (g•z)).re) := by
    have hs : Summable (fun g : gamma N => (upperEnergy u.toFun u.toFun (g•z)).re) := by
      apply summable_of_hasFiniteSupport
      apply (compact_orbit_point_finite (G := gamma N) K hK z).subset
      intro g hg
      apply hu
      apply upperEnergy_support_right u.toFun u.toFun
      intro hz
      exact hg (by change (upperEnergy u.toFun u.toFun (g•z)).re=0; rw [hz]; rfl)
    have hn (g : gamma N) : 0≤(upperEnergy u.toFun u.toFun (g•z)).re :=
      hyperbolicEnergy_self_nonneg _ _
    have hb := ENNReal.ofReal_le_ofReal (hM u hu z)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg M),ENNReal.ofReal_natCast,
      ENNReal.ofReal_tsum_of_nonneg hn hs] at hb
  calc
    _ ≤ ∫⁻ z, (M:ℝ≥0∞)*∑' g : gamma N,
        ENNReal.ofReal ((upperEnergy u.toFun u.toFun (g•z)).re) ∂quotientMeasure N :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp)]
      congr 1
      exact lintegral_poincare_unfold volume
        (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
        (density N) (density_measurable N) (density_orbit_sum N) _
        (Complex.continuous_re.comp (upperEnergy_continuous u.smooth u.smooth)).measurable.ennreal_ofReal

/-- The same estimate for ordinary nonnegative energy integrals. -/
theorem compact_poincare_gradient_integral_bound (N : ℕ) (K : Set ℍ) (hK : IsCompact K) :
    ∃ M : ℕ,∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      (∫ z,(upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re ∂quotientMeasure N)≤
        (M:ℝ)*∫ z : ℍ,(upperEnergy u.toFun u.toFun z).re := by
  obtain ⟨M,hM⟩ := compact_poincare_gradient_lintegral_bound N K hK
  refine ⟨M,?_⟩
  intro u hu
  have h1 : Integrable (fun z => (upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N u.toFun) z).re) (quotientMeasure N) := by
    simpa only [RCLike.re_to_complex] using
      (poincare_green_energy N u.smooth u.smooth u.compact u.compact).1.re
  have h2 : Integrable (fun z : ℍ => (upperEnergy u.toFun u.toFun z).re) := by
    simpa only [RCLike.re_to_complex] using (upperEnergy_integrable u.smooth u.smooth u.compact).re
  have hn1 : ∀ᵐ z ∂quotientMeasure N,0≤(upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N u.toFun) z).re :=
    Eventually.of_forall (fun _ => hyperbolicEnergy_self_nonneg _ _)
  have hn2 : ∀ᵐ z : ℍ,0≤(upperEnergy u.toFun u.toFun z).re :=
    Eventually.of_forall (fun _ => hyperbolicEnergy_self_nonneg _ _)
  have hb := hM u hu
  rw [←ofReal_integral_eq_lintegral_ofReal h1 hn1,
    ←ofReal_integral_eq_lintegral_ofReal h2 hn2,←ENNReal.ofReal_natCast,
    ←ENNReal.ofReal_mul (Nat.cast_nonneg M)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg M)
    (integral_nonneg_of_ae hn2))).mp hb

#print axioms compact_poincare_gradient_lintegral_bound
#print axioms compact_poincare_gradient_integral_bound

end QuantitativeMaass
