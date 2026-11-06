module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace FinitenessExponentialCutoff

/-- A deliberately non-optimal but linear cutoff. The exponential beats the
weight uniformly on the whole high-height tail, not merely at its endpoint. -/
theorem contraction (b : ℕ) {t a : ℝ} (ht : 2 ≤ t)
    (ha : (b : ℝ) + 1 ≤ a) :
    t^b * Real.exp (-a * (t-1)) ≤ Real.exp (-1) := by
  have ht0 : 0 ≤ t := by linarith
  have hbase : t ≤ Real.exp (t-1) := by
    simpa only [sub_add_cancel] using Real.add_one_le_exp (t-1)
  have hpow : t^b ≤ Real.exp ((b : ℝ)*(t-1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ ht0 hbase b
  calc
    t^b * Real.exp (-a*(t-1))
        ≤ Real.exp ((b : ℝ)*(t-1)) * Real.exp (-a*(t-1)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (((b : ℝ)-a)*(t-1)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)

theorem contraction_constant : 0 < Real.exp (-1) ∧ Real.exp (-1) < 1 := by
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num)⟩

/-- A polynomial times an exponential is bounded, with an explicit elementary
constant. This suffices to bound every positive-height weighted tail. -/
theorem polynomial_decay_bound (b : ℕ) {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    y^b * Real.exp (-a*y) ≤ (Nat.factorial b : ℝ) / a^b := by
  have hp := Real.pow_div_factorial_le_exp (a*y) (mul_nonneg ha.le hy) b
  have hf : 0 < (Nat.factorial b : ℝ) := by exact_mod_cast Nat.factorial_pos b
  have hp' : (a*y)^b ≤ Real.exp (a*y) * (Nat.factorial b : ℝ) :=
    (div_le_iff₀ hf).mp hp
  have hex : Real.exp (a*y) * Real.exp (-a*y) = 1 := by
    rw [← Real.exp_add, show a*y + -a*y = 0 by ring, Real.exp_zero]
  apply (le_div_iff₀ (pow_pos ha b)).mpr
  calc
    (y^b * Real.exp (-a*y)) * a^b
        = (a*y)^b * Real.exp (-a*y) := by rw [mul_pow]; ring
    _ ≤ (Real.exp (a*y) * (Nat.factorial b : ℝ)) * Real.exp (-a*y) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = (Nat.factorial b : ℝ) := by
      calc
        _ = (Nat.factorial b : ℝ) * (Real.exp (a*y) * Real.exp (-a*y)) := by ring
        _ = _ := by rw [hex, mul_one]

#print axioms contraction
#print axioms polynomial_decay_bound

end FinitenessExponentialCutoff
