module

public import QuantitativeHolomorphicDiagonalV1
public import QuantitativeHolomorphicFiniteBranchTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticBergmanDecay AsymptoticUnweightedKernel

theorem scalar_kernel_normalization_bound (I J : ℂ) {E A k : ℝ} (hk : 1 ≤ k)
    (hE : ‖I - J‖ ≤ E) (hA : ‖J‖ ≤ A) :
    |(k - 1) / k * I.re - J.re| ≤ E + A / k := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hp0 : 0 ≤ (k - 1) / k := div_nonneg (sub_nonneg.mpr hk) hkpos.le
  have hp1 : (k - 1) / k ≤ 1 := (div_le_one hkpos).mpr (by linarith)
  have he : (k - 1) / k * I.re - J.re = (k - 1) / k * (I.re - J.re) - J.re / k := by
    field_simp
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hp0, abs_div, abs_of_pos hkpos]
  have hd : |I.re - J.re| ≤ ‖I - J‖ := by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (I - J)
  have hdiff : |I.re - J.re| ≤ E := hd.trans hE
  have hreal : |J.re| ≤ A := (Complex.abs_re_le_norm J).trans hA
  exact add_le_add ((mul_le_of_le_one_left (abs_nonneg _) hp1).trans hdiff)
    (div_le_div_of_nonneg_right hreal hkpos.le)

def diagonalTraceError (Y H area : ℝ) (h : ℕ) : ℝ :=
  (compactKernelBound Y H 0 / (1 + (h : ℝ) / (4 * H ^ 2)) * area +
    area / ((2 * h + 2 : ℕ) : ℝ)) / (4 * Real.pi)

/-- The identity branch of the actual Fourier trace, with both the
periodization error and the exact `k-1` versus `k` correction. -/
theorem normalized_identity_branch_trace_bound
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hstrip : Ω ⊆ AsymptoticMassTransport.strip) (coeff : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    (hc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ 1)
    {Y H ε : ℝ} (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ᵐ z ∂volume.restrict Ω, Y ≤ z.im ∧ z.im ≤ H)
    (h : ℕ) (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] Ω.indicator
      (fun z => coeff z * z.im * unitRepresentative (2 * h) 0 n ε
        (AsymptoticStripCoordinates.cylinder z))) :
    |liftedTrace h hε W / ((2 * h + 2 : ℕ) : ℝ) - (∫ z in Ω, coeff z).re / (4 * Real.pi)| ≤
      diagonalTraceError Y H (volume.real Ω) h := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hreg : ∀ᵐ z ∂volume.restrict Ω, Y ≤ z.im ∧ Y ≤ z.im ∧ z.im ≤ H ∧ z.im ≤ H :=
    hregion.mono fun _ hz => ⟨hz.1, hz.1, hz.2, hz.2⟩
  have hi := periodized_diagonal_integral_error_bound (volume.restrict Ω) id measurable_id
    coeff hcmeas hc h hY hH hregion
  simp only [id_eq, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hi
  have hj := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) hc
  simp only [integral_const, smul_eq_mul, mul_one] at hj
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hj
  rw [branch_trace_periodized h hε hY (by norm_num : (0 : ℝ) ≤ 1)
    W Ω hΩ hstrip id measurable_id coeff hcmeas hc hreg hact]
  let I : ℂ := ∫ z in Ω, coeff z * (∑' n : ℤ, base (translate z n) z ^ (2 * h + 2))
  let J : ℂ := ∫ z in Ω, coeff z
  have hnorm := scalar_kernel_normalization_bound I J (k := ((2 * h + 2 : ℕ) : ℝ))
    (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) h]) hi hj
  have he : ((((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) -
      J.re / (4 * Real.pi)) =
      (((((2 * h + 2 : ℕ) : ℝ) - 1) / ((2 * h + 2 : ℕ) : ℝ)) * I.re - J.re) / (4 * Real.pi) := by
    push_cast
    ring
  change |((((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) -
      J.re / (4 * Real.pi))| ≤ _
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi)]
  exact div_le_div_of_nonneg_right hnorm (by positivity)

theorem normalized_identity_branch_trace_bound_of_cap
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hstrip : Ω ⊆ AsymptoticMassTransport.strip) (coeff : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ C)
    {Y H ε : ℝ} (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ᵐ z ∂volume.restrict Ω, Y ≤ z.im ∧ z.im ≤ H)
    (h : ℕ) (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] Ω.indicator
      (fun z => coeff z * z.im * unitRepresentative (2 * h) 0 n ε
        (AsymptoticStripCoordinates.cylinder z))) :
    |liftedTrace h hε W / ((2 * h + 2 : ℕ) : ℝ) - (∫ z in Ω, coeff z).re / (4 * Real.pi)| ≤
      C * diagonalTraceError Y H (volume.real Ω) h := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hreg : ∀ᵐ z ∂volume.restrict Ω, Y ≤ z.im ∧ Y ≤ z.im ∧ z.im ≤ H ∧ z.im ≤ H :=
    hregion.mono fun _ hz => ⟨hz.1, hz.1, hz.2, hz.2⟩
  have hi := periodized_diagonal_integral_error_bound_of_cap (volume.restrict Ω) id measurable_id
    coeff hcmeas hC hc h hY hH hregion
  simp only [id_eq, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hi
  have hj := norm_integral_le_of_norm_le (integrable_const C) hc
  simp only [integral_const, smul_eq_mul] at hj
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hj
  rw [branch_trace_periodized h hε hY hC
    W Ω hΩ hstrip id measurable_id coeff hcmeas hc hreg hact]
  let I : ℂ := ∫ z in Ω, coeff z * (∑' n : ℤ, base (translate z n) z ^ (2 * h + 2))
  let J : ℂ := ∫ z in Ω, coeff z
  have hnorm := scalar_kernel_normalization_bound I J (k := ((2 * h + 2 : ℕ) : ℝ))
    (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) h]) hi hj
  have he : ((((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) -
      J.re / (4 * Real.pi)) =
      (((((2 * h + 2 : ℕ) : ℝ) - 1) / ((2 * h + 2 : ℕ) : ℝ)) * I.re - J.re) / (4 * Real.pi) := by
    push_cast
    ring
  change |((((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) -
      J.re / (4 * Real.pi))| ≤ _
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 4 * Real.pi)]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ 4 * Real.pi)
    _ = C * diagonalTraceError Y H (volume.real Ω) h := by
      dsimp [diagonalTraceError, Measure.real]
      ring


#print axioms scalar_kernel_normalization_bound
#print axioms normalized_identity_branch_trace_bound

end QuantitativeHolomorphic
