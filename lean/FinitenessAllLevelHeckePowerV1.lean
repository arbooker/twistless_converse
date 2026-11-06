module

public import FinitenessAllLevelSharpTailV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelHeckePower

open Complex QuantitativeArithmeticRetainedReconstruction
  FinitenessAllLevelGoodTrace FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction

def scale (p m : ℕ) : ℂ := (p : ℂ) ^ m * (Real.sqrt p : ℂ)

theorem original_relation {N p : ℕ} (hp : p.Prime) (hgood : ¬ p ∣ N)
    (m : ℕ) {f : ℕ → ℂ} (hf : EulerData N f) {z : ℂ} (hz : 0 < z.im) :
    f p * fourier (fullCoefficients f (2 * m)) z =
      (scale p m)⁻¹ * completeTwist (fourier (fullCoefficients f (2 * m))) p (z / p) +
        ((scale p m)⁻¹ * (p : ℂ) ^ (2 * m)) *
          fourier (fullCoefficients f (2 * m)) ((p : ℂ) * z) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hs : scale p m ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0)
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos)).ne')
  have hz' : 0 < (z / (p : ℂ)).im := by
    simpa using div_pos hz (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p)
  have h := original_complete_even hf hp hgood m hz'
  have h₁ : (p : ℂ) * (z / p) = z := mul_div_cancel₀ z hp0
  have h₂ : (p : ℂ) ^ 2 * (z / p) = (p : ℂ) * z := by field_simp
  rw [h₁, h₂] at h
  change _ = scale p m * f p * _ - _ at h
  apply (mul_left_cancel₀ hs)
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  linear_combination -h

/-- Each application of the normalized Hecke eigenrelation lowers the
minimum sampled height by at most p. Constants do not depend on the eigenvalue. -/
theorem power_bound {p : ℕ} (hp : 1 ≤ p) (α β lam : ℂ) (G : ℂ → ℂ)
    (he : ∀ z : ℂ, 0 < z.im → lam * G z =
      α * completeTwist G p (z / p) + β * G ((p : ℂ) * z))
    (n : ℕ) {y M : ℝ} (hy : 0 < y)
    (hb : ∀ z : ℂ, y / (p : ℝ) ^ n ≤ z.im → ‖G z‖ ≤ M)
    {z : ℂ} (hz : y ≤ z.im) :
    ‖lam‖ ^ n * ‖G z‖ ≤ (‖α‖ * p + ‖β‖) ^ n * M := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  induction n generalizing y z with
  | zero => simpa only [pow_zero, one_mul] using hb z (by simpa only [pow_zero, div_one] using hz)
  | succ n ih =>
    let D := ‖α‖ * p + ‖β‖
    have hy' : 0 < y / (p : ℝ) := div_pos hy hp0
    have hbase : ∀ w : ℂ, (y / (p : ℝ)) / (p : ℝ) ^ n ≤ w.im → ‖G w‖ ≤ M := by
      intro w hw
      apply hb w
      simpa only [div_div, pow_succ', mul_comm] using hw
    have hshift (j : ℕ) : y / (p : ℝ) ≤ (z / (p : ℂ) + (j : ℂ) / p).im := by
      simpa using div_le_div_of_nonneg_right hz hp0.le
    have hdilate : y / (p : ℝ) ≤ ((p : ℂ) * z).im := by
      simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
      exact (div_le_self hy.le hp1).trans (hz.trans
        (le_mul_of_one_le_left (hy.trans_le hz).le hp1))
    have ht : ‖lam‖ ^ n * ‖completeTwist G p (z / p)‖ ≤ (p : ℝ) * (D ^ n * M) := by
      calc
        _ ≤ ‖lam‖ ^ n * ∑ j ∈ Finset.range p, ‖G (z / p + (j : ℂ) / p)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ = ∑ j ∈ Finset.range p, ‖lam‖ ^ n * ‖G (z / p + (j : ℂ) / p)‖ := by rw [Finset.mul_sum]
        _ ≤ ∑ _j ∈ Finset.range p, D ^ n * M :=
          Finset.sum_le_sum (fun j _ => ih hy' hbase (hshift j))
        _ = _ := by simp
    have hd := ih hy' hbase hdilate
    calc
      _ = ‖lam‖ ^ n * ‖lam * G z‖ := by rw [norm_mul, pow_succ]; ring
      _ ≤ ‖lam‖ ^ n * (‖α‖ * ‖completeTwist G p (z / p)‖ + ‖β‖ * ‖G ((p : ℂ) * z)‖) := by
        rw [he z (hy.trans_le hz)]
        exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using (norm_add_le
          (α * completeTwist G p (z / p)) (β * G ((p : ℂ) * z)))) (by positivity)
      _ = ‖α‖ * (‖lam‖ ^ n * ‖completeTwist G p (z / p)‖) +
          ‖β‖ * (‖lam‖ ^ n * ‖G ((p : ℂ) * z)‖) := by ring
      _ ≤ ‖α‖ * ((p : ℝ) * (D ^ n * M)) + ‖β‖ * (D ^ n * M) :=
        add_le_add (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
      _ = _ := by dsimp [D]; rw [pow_succ]; ring

#print axioms original_relation
#print axioms power_bound

end FinitenessAllLevelHeckePower
