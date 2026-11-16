module

public import QuantitativeArithmeticMaassExponentialCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassWeighted

/-- Pointwise squared-norm domination passes to the actual ambient L2 space. -/
theorem norm_sq_le_of_ae (N : ℕ) (f g : Lp ℂ 2 (quotientMeasure N)) (C : ℝ)
    (h : ∀ᵐ z ∂quotientMeasure N, ‖f z‖^2 ≤ C*‖g z‖^2) :
    ‖f‖^2 ≤ C*‖g‖^2 := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral f,
    AsymptoticL2Multiplier.norm_sq_eq_integral g, ← integral_const_mul]
  exact integral_mono_ae
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (((Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul C) h

theorem multiplier_ae (N : ℕ) (b : Cutoff N) (f : Lp ℂ 2 (quotientMeasure N)) :
    ∀ᵐ z ∂quotientMeasure N, multiplier N b f z=upperFunction b.value z*f z :=
  AsymptoticL2Multiplier.operator_coeFn _
    (upperFunction_continuous b.smooth).aestronglyMeasurable
    (Eventually.of_forall b.value_bound) f

theorem exponential_norm (N : ℕ) (b : Cutoff N) (a : ℝ) (z : ℍ) :
    ‖upperFunction (exponentialValue a b.value) z‖=
      Real.exp (a*(upperFunction b.value z).re) := by
  change ‖Complex.exp ((a:ℂ)*upperFunction b.value z)‖=_
  rw [Complex.norm_exp]
  simp

/-- An initial field supported in a sublevel set has the expected weighted norm. -/
theorem exponential_initial_bound (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    (f : Lp ℂ 2 (quotientMeasure N)) (c : ℝ)
    (hf : ∀ᵐ z ∂quotientMeasure N, c<(upperFunction b.value z).re → f z=0) :
    ‖multiplier N (exponentialCutoff N b a ha) f‖^2≤Real.exp (2*a*c)*‖f‖^2 := by
  apply norm_sq_le_of_ae
  filter_upwards [multiplier_ae N (exponentialCutoff N b a ha) f,hf] with z hz hs
  rw [hz,norm_mul,mul_pow]
  change ‖upperFunction (exponentialValue a b.value) z‖^2*‖f z‖^2≤_
  rw [exponential_norm]
  by_cases hc : (upperFunction b.value z).re≤c
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖f z‖)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hc ha]
  · rw [hs (lt_of_not_ge hc)]
    simp

/-- An observation supported in a superlevel set can be extracted from the
exponentially weighted field, with an exponentially small factor. -/
theorem exponential_observation_bound (N : ℕ) (b w : Cutoff N) {a : ℝ} (ha : 0≤a)
    (f : Lp ℂ 2 (quotientMeasure N)) (d : ℝ)
    (hw : ∀ᵐ z ∂quotientMeasure N,
      (upperFunction b.value z).re<d → upperFunction w.value z=0) :
    ‖multiplier N w f‖^2≤w.bound^2*Real.exp (-(2*a*d))*
      ‖multiplier N (exponentialCutoff N b a ha) f‖^2 := by
  apply norm_sq_le_of_ae
  filter_upwards [multiplier_ae N w f,
    multiplier_ae N (exponentialCutoff N b a ha) f,hw] with z hwz hbz hs
  rw [hwz,hbz,norm_mul,norm_mul,mul_pow,mul_pow]
  change ‖upperFunction w.value z‖^2*‖f z‖^2≤
    w.bound^2*Real.exp (-(2*a*d))*(‖upperFunction (exponentialValue a b.value) z‖^2*‖f z‖^2)
  rw [exponential_norm]
  by_cases hd : d≤(upperFunction b.value z).re
  · have he : 1≤Real.exp (-(2*a*d))*Real.exp (a*(upperFunction b.value z).re)^2 := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      norm_num only [Nat.cast_ofNat]
      nlinarith [mul_le_mul_of_nonneg_left hd ha]
    have hb := (sq_le_sq₀ (norm_nonneg _) w.bound_nonneg).mpr (w.value_bound z)
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg w.bound)
    have hh' := mul_le_mul_of_nonneg_right (hb.trans (by simpa using hh)) (sq_nonneg ‖f z‖)
    nlinarith only [hh']
  · rw [hs (lt_of_not_ge hd)]
    simp only [norm_zero,zero_pow (by omega : 2≠0),zero_mul]
    positivity

#print axioms exponential_initial_bound
#print axioms exponential_observation_bound

end QuantitativeMaass.Weighted
