module

public import FinitenessPolynomialSeriesV1
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FinitenessGrowthNormalization

open Filter Asymptotics FinitenessPolynomialSeries

/-- The Fourier coefficients are f_n TIMES n^((k-1)/2). -/
noncomputable def normalized (f : ℕ → ℂ) (α : ℝ) (n : ℕ) : ℂ :=
  f n * ((n : ℝ)^α : ℝ)

theorem normalized_zero {f : ℕ → ℂ} (hf0 : f 0 = 0) (α : ℝ) : normalized f α 0 = 0 := by
  simp only [normalized, hf0, zero_mul]

/-- An individual asymptotic real-exponent bound yields the integer-power
envelope used by the disk construction, after the required normalization. -/
theorem polynomial_bound {f : ℕ → ℂ} (hf0 : f 0 = 0) {σ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^σ)) (α : ℝ) :
    PolynomialBound (normalized f α) := by
  obtain ⟨C,hC,hbound⟩ := bound_of_isBigO_nat_atTop hf
  obtain ⟨d,hd⟩ := exists_nat_gt (σ+α)
  refine ⟨C,hC.le,d,?_⟩
  intro n
  by_cases hn0 : n=0
  · subst n
    rw [normalized_zero hf0, norm_zero]
    positivity
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpn : (n : ℝ)^σ ≠ 0 := (Real.rpow_pos_of_pos hn σ).ne'
  have hb : ‖f n‖ ≤ C*(n : ℝ)^σ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn σ)] using hbound hpn
  have hpow : (n : ℝ)^(σ+α) ≤ (n : ℝ)^d := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn1 hd.le
  calc
    ‖normalized f α n‖ = ‖f n‖*(n : ℝ)^α := by
      simp only [normalized, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hn α)]
    _ ≤ (C*(n : ℝ)^σ)*(n : ℝ)^α :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_pos_of_pos hn α).le
    _ = C*((n : ℝ)^(σ+α)) := by rw [Real.rpow_add hn, mul_assoc]
    _ ≤ C*(n : ℝ)^d := mul_le_mul_of_nonneg_left hpow hC.le
    _ ≤ C*(1+(n : ℝ)^d) := by nlinarith

#print axioms polynomial_bound

end FinitenessGrowthNormalization
