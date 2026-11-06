module

public import FinitenessAllLevelGoodFourierV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelGoodTrace

open Complex FinitenessFourierConstruction FinitenessOriginalInput
  FinitenessOriginalFourier QuantitativeArithmeticRetainedReconstruction

theorem first_weight {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (p : ℝ) * (p : ℝ) ^ FinitenessCompletedNormalization.alpha k =
      (p : ℝ) ^ (((k : ℝ) + 1) / 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [show ((k : ℝ) + 1) / 2 = 1 + FinitenessCompletedNormalization.alpha k by
    unfold FinitenessCompletedNormalization.alpha; ring]
  rw [Real.rpow_add hpR, Real.rpow_one]

theorem second_weight {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (p : ℝ) * ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k) ^ 2 =
      (p : ℝ) ^ k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    (p : ℝ) * ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k) ^ 2 =
        (p : ℝ) ^ (1 + (FinitenessCompletedNormalization.alpha k +
          FinitenessCompletedNormalization.alpha k)) := by
      rw [Real.rpow_add hpR, Real.rpow_add hpR, Real.rpow_one, pow_two]
    _ = (p : ℝ) ^ k := by
      rw [show 1 + (FinitenessCompletedNormalization.alpha k +
          FinitenessCompletedNormalization.alpha k) = (k : ℝ) by
        unfold FinitenessCompletedNormalization.alpha; ring]
      exact Real.rpow_natCast _ _

/-- The exact complete-trace equation in paper2, with its two dilations and
literal normalization, derived from the original Euler data. -/
theorem original_complete {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f k)) p z =
      (((p : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * f p *
        fourier (fullCoefficients f k) ((p : ℂ) * z) -
      (p : ℂ) ^ k * fourier (fullCoefficients f k) ((p : ℂ) ^ 2 * z) := by
  rw [FinitenessAllLevelGoodFourier.original_complete hf hp hgood k hz]
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) (first_weight hp.pos k)
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) (second_weight hp.pos k)
  push_cast at h1 h2
  rw [h2, show (p : ℂ) * (f p *
      ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ)) =
      ((p : ℂ) * ((p : ℝ) ^ FinitenessCompletedNormalization.alpha k : ℝ)) * f p by ring,
    h1]

noncomputable def firstMultiplier (f : ℕ → ℂ) (m p : ℕ) : ℂ :=
  (p : ℂ) ^ m * (Real.sqrt p : ℂ) * f p

theorem first_weight_even (p m : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ ((((2 * m : ℕ) : ℝ) + 1) / 2) =
      (p : ℝ) ^ m * Real.sqrt p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hpR]
  congr 1
  push_cast
  ring

theorem original_complete_even {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N) (m : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f (2 * m))) p z =
      firstMultiplier f m p * fourier (fullCoefficients f (2 * m)) ((p : ℂ) * z) -
      (p : ℂ) ^ (2 * m) * fourier (fullCoefficients f (2 * m)) ((p : ℂ) ^ 2 * z) := by
  rw [original_complete hf hp hgood (2 * m) hz, first_weight_even p m hp.pos]
  simp only [firstMultiplier, ofReal_mul, ofReal_pow, ofReal_natCast]

/-- After weighting by height to the power k/2, the sum of the two
dilation costs is sqrt(p)*|f_p|+1, independent of the weight. -/
theorem weighted_cost (f : ℕ → ℂ) (m : ℕ) {p : ℕ} (hp : 0 < p) :
    ‖firstMultiplier f m p‖ / (p : ℝ) ^ m +
      ‖(p : ℂ) ^ (2 * m)‖ / ((p : ℝ) ^ 2) ^ m =
      Real.sqrt p * ‖f p‖ + 1 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [firstMultiplier, norm_mul, norm_pow, norm_natCast,
    norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← pow_mul]
  field_simp

#print axioms original_complete
#print axioms original_complete_even
#print axioms weighted_cost

end FinitenessAllLevelGoodTrace
