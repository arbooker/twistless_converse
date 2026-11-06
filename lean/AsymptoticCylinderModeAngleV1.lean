module

public import AsymptoticCylinderModeComparisonV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderModeComparison

open MeasureTheory Set AsymptoticCylinder AsymptoticFourierNorm AsymptoticGammaTail

/-- The weighted/unweighted Fourier-mode comparison in the paper, proved
for the actual unit modes in the common flat L² realization. The bound is
uniform in frequency, positive scale, and positive cap height. -/
theorem unitMode_distance_sq_le (m t n : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) :
    ‖unitMode m t n hs hε - unitMode m 0 n hs hε‖^2 ≤
      4 * (((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1) := by
  let r : ℝ := scale*(n+1:ℕ)
  have hr : 0 < r := mul_pos hs (by positivity)
  let B : ℝ := beta m 0 r ε
  have hB : 0 < B := beta_pos m 0 hr hε
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  let v : Space := ((Real.sqrt B)⁻¹ : ℂ) • meanScaledMode m t n hs hε
  let u : Space := unitMode m 0 n hs hε
  have hu : ‖u‖ = 1 := by
    have hh := unitMode_norm_sq m 0 n hs hε
    have hn := norm_nonneg u
    change ‖u‖^2 = 1 at hh
    nlinarith
  have hraw : modeLp m t n hs hε ≠ 0 := by
    intro he
    have hh := modeLp_norm_sq m t n hs hε
    rw [he, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hh
    have hp := beta_pos m t hr hε
    change 0 < beta m t (scale*(n+1:ℕ)) ε at hp
    linarith
  have hc : 0 < meanCap m t r ε := meanCap_pos m t hr hε
  have hv : v ≠ 0 := by
    exact smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hsqrt.ne'))
      (smul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')) hraw)
  have hvn : normalize v = unitMode m t n hs hε := by
    rw [show v = ((Real.sqrt B)⁻¹ : ℂ) • meanScaledMode m t n hs hε from rfl,
      ← Complex.ofReal_inv, normalize_smul_pos _ (inv_pos.mpr hsqrt), meanScaledMode,
      ← Complex.ofReal_inv, normalize_smul_pos _ (inv_pos.mpr hc), normalize_mode]
  have herr : ‖v-u‖^2 ≤ (((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1) := by
    have hu' : u = ((Real.sqrt B)⁻¹ : ℂ) • modeLp m 0 n hs hε := by
      simp only [u, unitMode, B, r]
    have he : ‖v-u‖^2 = B⁻¹ * ‖meanScaledMode m t n hs hε - modeLp m 0 n hs hε‖^2 := by
      rw [hu']
      change ‖((Real.sqrt B)⁻¹ : ℂ) • meanScaledMode m t n hs hε -
        ((Real.sqrt B)⁻¹ : ℂ) • modeLp m 0 n hs hε‖^2 = _
      rw [← smul_sub, norm_smul, mul_pow]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
        inv_pow, Real.sq_sqrt hB.le]
    have hb : B = ∫ y in Ioi 0, kernel m r y := by
      simp only [B, beta, density, Nat.mul_zero, pow_zero, mul_one]
    rw [he, meanScaledMode_error_sq, hb]
    simpa only [div_eq_mul_inv, mul_comm] using
      AsymptoticCappedGamma.ratio_squared_error_bound m t hr hε
  have hn := normalize_sub_unit_le u v hu hv
  rw [hvn] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  change ‖unitMode m t n hs hε - u‖^2 ≤ _
  calc
    _ ≤ (2 * ‖v-u‖)^2 := hsq
    _ = 4 * ‖v-u‖^2 := by ring
    _ ≤ 4 * ((((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = _ := by ring

#print axioms unitMode_distance_sq_le

end AsymptoticCylinderModeComparison
