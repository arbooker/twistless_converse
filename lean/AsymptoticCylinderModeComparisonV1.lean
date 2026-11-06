module

public import AsymptoticCappedGammaV1
public import AsymptoticCylinderWeightV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderModeComparison

open MeasureTheory Set AsymptoticCylinder AsymptoticFourierNorm AsymptoticGammaTail

noncomputable def normalize {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (v : G) : G := (‖v‖ : ℂ)⁻¹ • v

theorem normalize_smul_pos {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (v : G) {c : ℝ} (hc : 0 < c) : normalize ((c : ℂ) • v) = normalize v := by
  simp only [normalize, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc, Complex.ofReal_mul, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), mul_one]

theorem normalize_sub_unit_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (u v : G) (hu : ‖u‖ = 1) (hv : v ≠ 0) :
    ‖normalize v - u‖ ≤ 2 * ‖v-u‖ := by
  have hv0 : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have he : ‖normalize v - v‖ = |1 - ‖v‖| := by
    unfold normalize
    rw [show (‖v‖ : ℂ)⁻¹ • v - v = ((‖v‖ : ℂ)⁻¹ - 1) • v by rw [sub_smul, one_smul],
      norm_smul]
    calc
      _ = ‖((‖v‖ : ℂ)⁻¹ - 1) * (‖v‖ : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = _ := by
        rw [sub_mul, inv_mul_cancel₀ hv0, one_mul]
        norm_cast
  have hd : |1 - ‖v‖| ≤ ‖v-u‖ := by
    rw [abs_sub_comm, ← hu]
    exact abs_norm_sub_norm_le v u
  calc
    _ ≤ ‖normalize v - v‖ + ‖v-u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖v-u‖ := by rw [he]; linarith

theorem normalize_mode (m t n : ℕ) {scale ε : ℝ} (hs : 0 < scale) (hε : 0 < ε) :
    normalize (modeLp m t n hs hε) = unitMode m t n hs hε := by
  have hn : ‖modeLp m t n hs hε‖ = Real.sqrt (beta m t (scale*(n+1:ℕ)) ε) := by
    rw [← modeLp_norm_sq m t n hs hε, Real.sqrt_sq (norm_nonneg _)]
  simp only [normalize, hn, unitMode]

theorem mode_weight_factor (m t n : ℕ) {scale ε : ℝ} (hε : 0 < ε)
    {z : Cylinder} (hz : 0 ≤ z.2) :
    mode m t n scale ε z = ((min (z.2/ε) 1)^t : ℝ) • mode m 0 n scale ε z := by
  have hc : 0 ≤ (min (z.2/ε) 1)^t := by positivity
  have hd : density m t (scale*(n+1:ℕ)) ε z.2 =
      kernel m (scale*(n+1:ℕ)) z.2 * ((min (z.2/ε) 1)^t)^2 := by
    simp only [density, ← pow_mul]
    congr 2
    omega
  rw [mode, hd, Real.sqrt_mul (kernel_nonneg m _ hz), Real.sqrt_sq hc]
  simp only [mode, density, Nat.mul_zero, pow_zero, mul_one, Complex.ofReal_mul,
    Complex.real_smul]
  ring

noncomputable def meanCap (m t : ℕ) (r ε : ℝ) : ℝ :=
  (min (((m : ℝ)+1)/(r*ε)) 1)^t

theorem meanCap_pos (m t : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    0 < meanCap m t r ε := by unfold meanCap; positivity

/-- Before unit normalization, divide the weighted mode by its cap value
at the mean height of the unweighted radial gamma density. -/
noncomputable def meanScaledMode (m t n : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) : Space :=
  ((meanCap m t (scale*(n+1:ℕ)) ε)⁻¹ : ℂ) • modeLp m t n hs hε

theorem meanScaledMode_error_sq (m t n : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) :
    ‖meanScaledMode m t n hs hε - modeLp m 0 n hs hε‖^2 =
      ∫ y in Ioi 0, (AsymptoticCappedGamma.ratio m t (scale*(n+1:ℕ)) ε y - 1)^2 *
        kernel m (scale*(n+1:ℕ)) y := by
  let r : ℝ := scale*(n+1:ℕ)
  let c : ℝ := meanCap m t r ε
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  calc
    _ = ∫ z, (AsymptoticCappedGamma.ratio m t r ε z.2 - 1)^2 * kernel m r z.2 ∂measure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (meanScaledMode m t n hs hε) (modeLp m 0 n hs hε),
        Lp.coeFn_smul (c⁻¹ : ℂ) (modeLp m t n hs hε),
        modeLp_coeFn m t n hs hε, modeLp_coeFn m 0 n hs hε, height_positive]
        with z hsub hsm ht h0 hz
      rw [hsub]
      change ‖((c⁻¹ : ℂ) • modeLp m t n hs hε) z - (modeLp m 0 n hs hε) z‖^2 = _
      rw [hsm, Pi.smul_apply, ht, h0, mode_weight_factor m t n hε hz.le]
      simp only [smul_eq_mul, Complex.real_smul]
      have he : (c⁻¹ : ℂ) * ((↑((min (z.2/ε) 1)^t)) * mode m 0 n scale ε z) -
          mode m 0 n scale ε z =
          ((AsymptoticCappedGamma.ratio m t r ε z.2 - 1 : ℝ) : ℂ) * mode m 0 n scale ε z := by
        dsimp [AsymptoticCappedGamma.ratio, c, meanCap]
        push_cast
        ring
      rw [he, norm_mul, mul_pow, mode_norm_sq m 0 n scale hε hz.le]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, density,
        Nat.mul_zero, pow_zero, mul_one, r]
    _ = _ := by
      have hh := integral_prod_mul (μ:=AddCircle.haarAddCircle (T:=1))
        (ν:=volume.restrict (Ioi 0)) (fun _ : AddCircle (1:ℝ) => (1:ℝ))
        (fun y => (AsymptoticCappedGamma.ratio m t r ε y - 1)^2 * kernel m r y)
      simpa [AsymptoticCylinder.measure, r] using hh

#print axioms normalize_sub_unit_le
#print axioms meanScaledMode_error_sq

end AsymptoticCylinderModeComparison
