module

public import FinitenessAllLevelMellinDirichletV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelMellinNormalization

open Complex Filter Asymptotics MeasureTheory FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay FinitenessAllLevelMellinDirichlet

def constant (N k : ℕ) : ℂ := 2 * (N : ℂ) ^ (-(k : ℂ) / 4)

def completion (N k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  constant N k * mellin (axis N (fullCoefficients f k)) (s + ((k : ℂ) - 1) / 2)

theorem sqrt_cpow {N : ℕ} (hN : 0 < N) (w : ℂ) :
    (Real.sqrt N : ℂ) ^ w = (N : ℂ) ^ (w / 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := Real.sqrt_pos.mpr hNR
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hs.ne'), cpow_def_of_ne_zero hNC,
    ← ofReal_log hs.le, Real.log_sqrt hNR.le, ← natCast_log]
  congr 1
  push_cast
  ring

theorem scalar_normalization {N : ℕ} (hN : 0 < N) (k : ℕ) (s : ℂ) :
    constant N k * (rate N : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) =
      (N : ℂ) ^ ((s - 1 / 2) / 2) * 2 *
        ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := Real.sqrt_nonneg (N : ℝ)
  rw [rate, ofReal_div, Complex.div_cpow_ofReal_nonneg (by positivity) hs,
    div_eq_mul_inv, ← cpow_neg, neg_neg, sqrt_cpow hN]
  unfold constant
  calc
    _ = 2 * ((N : ℂ) ^ (-(k : ℂ) / 4) *
        (N : ℂ) ^ ((s + ((k : ℂ) - 1) / 2) / 2)) *
        ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) := by ring
    _ = _ := by
      rw [← cpow_add _ _ hNC]
      rw [show -(k : ℂ) / 4 + (s + ((k : ℂ) - 1) / 2) / 2 = (s - 1 / 2) / 2 by ring]
      ring

theorem coefficient_normalization (f : ℕ → ℂ) (k : ℕ) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    fullCoefficients f k n * (n : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) =
      f n * (n : ℂ) ^ (-s) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [fullCoefficients, FinitenessGrowthNormalization.normalized,
    Complex.ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast, mul_assoc, ← cpow_add _ _ hnC]
  congr 2
  unfold FinitenessCompletedNormalization.alpha
  push_cast
  ring

/-- The split-Mellin candidate agrees with the literal completion on a
right half-plane. The coefficient-growth exponent may be individual. -/
theorem completion_eq {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) {τ : ℝ} (hg : f =O[atTop] (fun n : ℕ => (n : ℝ) ^ τ)) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → completion N k f s = completed N k f s := by
  have ha := polynomial_bound hf0 hg k
  obtain ⟨d, hd⟩ := polynomial_growth ha
  refine ⟨(d : ℝ) + 2 + |FinitenessCompletedNormalization.alpha k|, ?_⟩
  intro s hs
  let w : ℂ := s + ((k : ℂ) - 1) / 2
  have hwre : w.re = s.re + FinitenessCompletedNormalization.alpha k := by
    simp [w, FinitenessCompletedNormalization.alpha, Complex.div_ofNat_re]
  have hw : (d : ℝ) + 1 < w.re := by
    rw [hwre]
    linarith [neg_abs_le (FinitenessCompletedNormalization.alpha k)]
  have hw0 : 0 < w.re := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hm := axis_mellin hN ha (fullCoefficients_zero hf0 k) hw0
    (summable_norm_div hd hw)
  unfold completion
  rw [hm]
  simp only [w, coefficient_normalization f k (Nat.succ_pos _)]
  change constant N k * (Gamma w * (rate N : ℂ) ^ (-w) * L f s) = _
  calc
    _ = (constant N k * (rate N : ℂ) ^ (-w)) * Gamma w * L f s := by ring
    _ = _ := by
      rw [scalar_normalization hN k s]
      unfold completed gammaC
      dsimp [w]
      ring

#print axioms scalar_normalization
#print axioms coefficient_normalization
#print axioms completion_eq

end FinitenessAllLevelMellinNormalization
