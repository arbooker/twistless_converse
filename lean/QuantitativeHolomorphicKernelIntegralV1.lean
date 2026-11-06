module

public import QuantitativeHolomorphicBergmanV1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory Set UpperHalfPlane AsymptoticBergmanDecay

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- A quantitative near/far decomposition, with no continuity assumption
on the coefficient function. -/
theorem norm_integral_near_far (f : α → ℂ) {E : Set α} (hE : MeasurableSet E)
    {ε : ℝ} (hε : 0 ≤ ε) (hcap : ∀ x, ‖f x‖ ≤ 1)
    (hfar : ∀ x, x ∉ E → ‖f x‖ ≤ ε) :
    ‖∫ x, f x ∂μ‖ ≤ μ.real E + ε * μ.real univ := by
  have hI := (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ).indicator hE
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ E.indicator (fun _ => (1 : ℝ)) x + ε := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      linarith [hcap x]
    · rw [indicator_of_notMem hx, zero_add]
      exact hfar x hx
  have hh := norm_integral_le_of_norm_le (hI.add (integrable_const ε)) hbound
  simpa only [Pi.add_apply, integral_add hI (integrable_const ε),
    integral_indicator_const (1 : ℝ) hE, integral_const, smul_eq_mul, mul_one,
    mul_comm (μ.real univ)] using hh

/-- A quantitative near/far decomposition, with no continuity assumption
on the coefficient function. -/
theorem norm_integral_near_far_ae (f : α → ℂ) {E : Set α} (hE : MeasurableSet E)
    {ε : ℝ} (hε : 0 ≤ ε) (hcap : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1)
    (hfar : ∀ᵐ x ∂μ, x ∉ E → ‖f x‖ ≤ ε) :
    ‖∫ x, f x ∂μ‖ ≤ μ.real E + ε * μ.real univ := by
  have hI := (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ).indicator hE
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ E.indicator (fun _ => (1 : ℝ)) x + ε := by
    filter_upwards [hcap, hfar] with x hcx hfx
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      linarith [hcx]
    · rw [indicator_of_notMem hx, zero_add]
      exact hfx hx
  have hh := norm_integral_le_of_norm_le (hI.add (integrable_const ε)) hbound
  simpa only [Pi.add_apply, integral_add hI (integrable_const ε),
    integral_indicator_const (1 : ℝ) hE, integral_const, smul_eq_mul, mul_one,
    mul_comm (μ.real univ)] using hh

theorem inverse_cube_root_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
  have he : ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num [Real.rpow_neg_one]
  rw [he, mul_inv_cancel₀ (by exact_mod_cast hn.ne')]

/-- A linear displacement-sublevel estimate gives a genuine uniform
power saving for a branch integral.  The arithmetic/geometric proof of
the sublevel hypothesis is deliberately not hidden in this theorem. -/
theorem bergman_integral_of_sublevel (z u : α → ℍ) (c : α → ℂ)
    {H A r : ℝ} (hH : 0 < H) (hr : 0 < r) (n : ℕ)
    (hscale : (n : ℝ) * r ^ 3 = 1)
    (hc : ∀ x, ‖c x‖ ≤ 1) (hheight : ∀ x, (z x).im * (u x).im ≤ H ^ 2)
    (hE : MeasurableSet {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r})
    (hsub : μ.real {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r} ≤ A * r) :
    ‖∫ x, c x * base (z x) (u x) ^ (2 * n) ∂μ‖ ≤
      (A + 4 * H ^ 2 * μ.real univ) * r := by
  have htail : 1 / (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) ≤ 4 * H ^ 2 * r := by
    have hden : 0 < 1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2) := by positivity
    apply (div_le_iff₀ hden).mpr
    have he : 4 * H ^ 2 * r * (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) =
        4 * H ^ 2 * r + (n : ℝ) * r ^ 3 := by
      field_simp
    rw [he, hscale]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * H ^ 2) hr.le]
  have hb := norm_integral_near_far μ
    (fun x => c x * base (z x) (u x) ^ (2 * n)) hE
    (ε := 4 * H ^ 2 * r) (by positivity) ?_ ?_
  · calc
      _ ≤ μ.real {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r} +
          (4 * H ^ 2 * r) * μ.real univ := hb
      _ ≤ A * r + (4 * H ^ 2 * r) * μ.real univ := add_le_add hsub le_rfl
      _ = _ := by ring
  · intro x
    rw [norm_mul, norm_pow]
    have hpow : ‖base (z x) (u x)‖ ^ (2 * n) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_base_le_one _ _)
    exact (mul_le_mul_of_nonneg_right (hc x) (by positivity)).trans
      (by simpa using hpow)
  · intro x hx
    rw [norm_mul, norm_pow]
    have hdist : r ≤ ‖(z x : ℂ) - (u x : ℂ)‖ := le_of_not_gt hx
    calc
      ‖c x‖ * ‖base (z x) (u x)‖ ^ (2 * n) ≤ ‖base (z x) (u x)‖ ^ (2 * n) :=
        mul_le_of_le_one_left (by positivity) (hc x)
      _ ≤ 1 / (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) :=
        bergman_even_power_bound _ _ hr.le hH hdist (hheight x) n
      _ ≤ _ := htail

/-- A linear displacement-sublevel estimate gives a genuine uniform
power saving for a branch integral.  The arithmetic/geometric proof of
the sublevel hypothesis is deliberately not hidden in this theorem. -/
theorem bergman_integral_of_sublevel_ae (z u : α → ℍ) (c : α → ℂ)
    {H A r : ℝ} (hH : 0 < H) (hr : 0 < r) (n : ℕ)
    (hscale : (n : ℝ) * r ^ 3 = 1)
    (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ 1) (hheight : ∀ᵐ x ∂μ, (z x).im * (u x).im ≤ H ^ 2)
    (hE : MeasurableSet {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r})
    (hsub : μ.real {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r} ≤ A * r) :
    ‖∫ x, c x * base (z x) (u x) ^ (2 * n) ∂μ‖ ≤
      (A + 4 * H ^ 2 * μ.real univ) * r := by
  have htail : 1 / (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) ≤ 4 * H ^ 2 * r := by
    have hden : 0 < 1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2) := by positivity
    apply (div_le_iff₀ hden).mpr
    have he : 4 * H ^ 2 * r * (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) =
        4 * H ^ 2 * r + (n : ℝ) * r ^ 3 := by
      field_simp
    rw [he, hscale]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * H ^ 2) hr.le]
  have hb := norm_integral_near_far_ae μ
    (fun x => c x * base (z x) (u x) ^ (2 * n)) hE
    (ε := 4 * H ^ 2 * r) (by positivity) ?_ ?_
  · calc
      _ ≤ μ.real {x | ‖(z x : ℂ) - (u x : ℂ)‖ < r} +
          (4 * H ^ 2 * r) * μ.real univ := hb
      _ ≤ A * r + (4 * H ^ 2 * r) * μ.real univ := add_le_add hsub le_rfl
      _ = _ := by ring
  · filter_upwards [hc] with x hcx
    rw [norm_mul, norm_pow]
    have hpow : ‖base (z x) (u x)‖ ^ (2 * n) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_base_le_one _ _)
    exact (mul_le_mul_of_nonneg_right hcx (by positivity)).trans
      (by simpa using hpow)
  · filter_upwards [hc, hheight] with x hcx hhx
    intro hx
    rw [norm_mul, norm_pow]
    have hdist : r ≤ ‖(z x : ℂ) - (u x : ℂ)‖ := le_of_not_gt hx
    calc
      ‖c x‖ * ‖base (z x) (u x)‖ ^ (2 * n) ≤ ‖base (z x) (u x)‖ ^ (2 * n) :=
        mul_le_of_le_one_left (by positivity) hcx
      _ ≤ 1 / (1 + (n : ℝ) * r ^ 2 / (4 * H ^ 2)) :=
        bergman_even_power_bound _ _ hr.le hH hdist hhx n
      _ ≤ _ := htail

theorem bergman_integral_cube_root_bound (z u : α → ℍ) (c : α → ℂ)
    {H A : ℝ} (hH : 0 < H) (n : ℕ) (hn : 0 < n)
    (hc : ∀ x, ‖c x‖ ≤ 1) (hheight : ∀ x, (z x).im * (u x).im ≤ H ^ 2)
    (hE : MeasurableSet {x | ‖(z x : ℂ) - (u x : ℂ)‖ < (n : ℝ) ^ (-(1 / 3 : ℝ))})
    (hsub : μ.real {x | ‖(z x : ℂ) - (u x : ℂ)‖ < (n : ℝ) ^ (-(1 / 3 : ℝ))} ≤
      A * (n : ℝ) ^ (-(1 / 3 : ℝ))) :
    ‖∫ x, c x * base (z x) (u x) ^ (2 * n) ∂μ‖ ≤
      (A + 4 * H ^ 2 * μ.real univ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
  bergman_integral_of_sublevel μ z u c hH
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) n
    (inverse_cube_root_identity n hn) hc hheight hE hsub

#print axioms norm_integral_near_far_ae
#print axioms bergman_integral_of_sublevel_ae
#print axioms norm_integral_near_far
#print axioms bergman_integral_of_sublevel
#print axioms bergman_integral_cube_root_bound

end QuantitativeHolomorphic
