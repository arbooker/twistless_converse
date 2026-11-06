module

public import QuantitativeArithmeticRamifiedFullTraceV1
public import FinitenessOriginalFrickeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open Complex FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedReconstruction

def scaledFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z/6)

/-- A squared ramified prime gives a zero complete additive average, directly
from the literal Euler input, at every weight. -/
theorem square_prime_average_zero {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hpsq : p^2 ∣ N) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    completeTwist (fourier (fullCoefficients f k)) p z=0 := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) hpsq
  have hh := QuantitativeArithmeticRamifiedFullTrace.original_complete hf hp hpN k hz
  have hzcoeff : fullCoefficients f k p=0 := by
    simp only [fullCoefficients, FinitenessGrowthNormalization.normalized,
      FinitenessOriginalTwistLocal.bad_parameter_zero hf hp hpsq, zero_mul]
  simpa only [hzcoeff, mul_zero, zero_mul] using hh

theorem scaled_antiperiod_three {f : ℕ → ℂ} (hf : EulerData 36 f) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) : scaledFourier k f (z+3) = -scaledFourier k f z := by
  have hh := square_prime_average_zero hf (p := 2) (by decide) (by decide) k
    (z := z/6) (by simpa using div_pos hz (by norm_num : (0:ℝ)<6))
  norm_num [completeTwist, Finset.sum_range_succ] at hh
  have he : (z+3)/6=z/6+(1:ℂ)/2 := by ring
  dsimp [scaledFourier]
  rw [he]
  linear_combination hh

/-- The full T²-T+1 relation for the scaled original Fourier function.
Both bad-prime equations are used, with no modularity hypothesis. -/
theorem scaled_translation_quadratic {f : ℕ → ℂ} (hf : EulerData 36 f) (k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    scaledFourier k f (z+2)-scaledFourier k f (z+1)+scaledFourier k f z=0 := by
  have hh := square_prime_average_zero hf (p := 3) (by decide) (by decide) k
    (z := z/6) (by simpa using div_pos hz (by norm_num : (0:ℝ)<6))
  norm_num [completeTwist, Finset.sum_range_succ] at hh
  have ha := scaled_antiperiod_three hf k (z := z+1) (by simpa using hz)
  have h2 : (z+2)/6=z/6+(1:ℂ)/3 := by ring
  have h4 : ((z+1)+3)/6=z/6+(2:ℂ)/3 := by ring
  dsimp [scaledFourier] at ha ⊢
  rw [h4] at ha
  rw [h2]
  linear_combination hh-ha

#print axioms square_prime_average_zero
#print axioms scaled_antiperiod_three
#print axioms scaled_translation_quadratic

end SmallLevelThirtySix
