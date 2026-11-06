module

public import SmallLevelIntegratedCauchyV1
public import SmallLevelRealSeriesUniquenessV1
public import SmallLevelAdditiveConvergenceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Set MeasureTheory FormalMultilinearSeries FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped NNReal ENNReal Topology

theorem deformed_real (k : ℕ) (a : ℕ → ℂ) (β c y t : ℝ) :
    deformed k a β c y (t:ℂ)=((1+(t:ℂ))^k)⁻¹*
      fourier a ((β:ℂ)+((((1+t)⁻¹*y)/c:ℝ):ℂ)*I) := by
  unfold deformed deformPoint
  congr 2
  push_cast
  ring

theorem deformed_real_mellin (k : ℕ) (a : ℕ → ℂ) (β c : ℝ) (s : ℂ)
    {t : ℝ} (ht : 0<1+t) :
    mellin (fun y => deformed k a β c y (t:ℂ)) s=
      mellin (fun y : ℝ => fourier a ((β:ℂ)+((y/c:ℝ):ℂ)*I)) s*
        (1+(t:ℂ))^(s-(k:ℂ)) := by
  simp_rw [deformed_real]
  have hm := mellin_const_smul
    (fun y : ℝ => fourier a ((β:ℂ)+((((1+t)⁻¹*y)/c:ℝ):ℂ)*I)) s (((1+(t:ℂ))^k)⁻¹)
  simp only [smul_eq_mul] at hm
  rw [hm]
  rw [mellin_comp_mul_left (fun y : ℝ => fourier a ((β:ℂ)+((y/c:ℝ):ℂ)*I)) s (inv_pos.mpr ht),
    Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg ht.le,← Complex.cpow_neg,neg_neg]
  rw [Complex.cpow_sub _ _ (by exact_mod_cast ne_of_gt ht),Complex.cpow_natCast]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- Every Cauchy coefficient has the predicted Mellin transform. This
identifies all Taylor orders, not just the constant term. -/
theorem taylorCoeff_mellin (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β : ℝ, ∀ s : ℂ, (K:ℝ)<s.re → ∀ n : ℕ,
      mellin (fun y => taylorCoeff k a β c y n) s=
        Ring.choose (s-(k:ℂ)) n*
          mellin (fun y : ℝ => fourier a ((β:ℂ)+((y/c:ℝ):ℂ)*I)) s := by
  obtain ⟨K,hK⟩ := deformed_mellin_series k ha ha0 hc
  refine ⟨K,?_⟩
  intro β s hs n
  have h := coefficients_of_real_binomial (hK β s hs).hasFPowerSeriesAt
    (mellin (fun y : ℝ => fourier a ((β:ℂ)+((y/c:ℝ):ℂ)*I)) s)
    (s-(k:ℂ)) (δ := 1) (by norm_num)
    (fun t ht _ => deformed_real_mellin k a β c s (by linarith)) n
  simpa only [coeff_ofScalars,mul_comm] using h

theorem scaled_ray_mellin (a : ℕ → ℂ) (β : ℝ) {c : ℝ} (hc : 0<c) (s : ℂ) :
    mellin (fun y : ℝ => fourier a ((β:ℂ)+((y/c:ℝ):ℂ)*I)) s=
      (c:ℂ)^s*mellin (fun y : ℝ => fourier a ((β:ℂ)+(y:ℂ)*I)) s := by
  simp only [div_eq_inv_mul]
  rw [mellin_comp_mul_left (fun y : ℝ => fourier a ((β:ℂ)+(y:ℂ)*I)) s (inv_pos.mpr hc),
    Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg hc.le,← Complex.cpow_neg,neg_neg,smul_eq_mul]

/-- Literal all-order coefficient identity in terms of the additive
Dirichlet transform, with the precise scale and complex binomial factor. -/
theorem taylorCoeff_additive_mellin (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ B : ℝ, ∀ β : ℝ, ∀ s : ℂ, B<s.re → ∀ n : ℕ,
      mellin (fun y => taylorCoeff k a β c y n) s=
        Ring.choose (s-(k:ℂ)) n*(c:ℂ)^s*SmallLevelAdditive.transform a β s := by
  obtain ⟨K,hK⟩ := taylorCoeff_mellin k ha ha0 hc
  obtain ⟨B,hB⟩ := additive_convergence_halfplane ha ha0
  refine ⟨max (K:ℝ) B,?_⟩
  intro β s hs n
  rw [hK β s (lt_of_le_of_lt (le_max_left _ _) hs) n,scaled_ray_mellin a β hc s,
    (hB β s (lt_of_le_of_lt (le_max_right _ _) hs)).2,mul_assoc]

#print axioms deformed_real_mellin
#print axioms taylorCoeff_mellin
#print axioms taylorCoeff_additive_mellin
end SmallLevelTaylor
