module

public import QuantitativeHolomorphicBranchIntegralV1
public import QuantitativeHolomorphicPeriodizationV1
public import AsymptoticNonreturningBranchTraceV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticBergmanDecay AsymptoticUnweightedKernel

theorem conj_base (z u : ℍ) : star (base z u) = base u z := by
  simp only [base, star_div₀, star_mul, star_ofNat, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, map_sub, Complex.conj_conj]
  rw [mul_comm u.im z.im]
  rw [show (starRingEnd ℂ) (z : ℂ) - (u : ℂ) = -((u : ℂ) - (starRingEnd ℂ) (z : ℂ)) by ring,
    div_neg]
  ring

theorem integral_base_reverse_norm {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (z u : α → ℍ) (coeff : α → ℂ) (k : ℕ) :
    ‖∫ x, coeff x * base (u x) (z x) ^ k ∂μ‖ =
      ‖∫ x, star (coeff x) * base (z x) (u x) ^ k ∂μ‖ := by
  have he : (∫ x, coeff x * base (u x) (z x) ^ k ∂μ) =
      star (∫ x, star (coeff x) * base (z x) (u x) ^ k ∂μ) := by
    change _ = (starRingEnd ℂ) _
    rw [← integral_conj]
    change (∫ x, coeff x * base (u x) (z x) ^ k ∂μ) =
      ∫ x, star (star (coeff x) * base (z x) (u x) ^ k) ∂μ
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [star_mul, star_star, star_pow, conj_base]
    ring
  rw [he, norm_star]

/-- The normalized trace prefactor is uniformly bounded by `1/(4π)`.
This is the exact finite-weight ratio, not only its limiting value. -/
theorem normalized_trace_prefactor_bound (h : ℕ) :
    0 ≤ (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi)) / ((2 * h + 2 : ℕ) : ℝ) ∧
    (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi)) / ((2 * h + 2 : ℕ) : ℝ) ≤
      1 / (4 * Real.pi) := by
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity : 0 < ((2 * h + 2 : ℕ) : ℝ))]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * Real.pi)).mpr
    push_cast
    linarith

theorem translated_branch_integral_bound
    (a b c d j : ℤ) (hdet : a * d - b * c ≠ 0)
    (hne : c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (u : ℍ → ℍ) (hu : Measurable u) (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (coeff : ℍ → ℂ)
    (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ 1)
    {D Y H : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (hlower : ∀ z ∈ Ω, Y ≤ z.im)
    (hupper : ∀ z ∈ Ω, z.im * (u z).im ≤ H ^ 2)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1) :
    ‖∫ z in Ω, coeff z * base (translate (u z) j) z ^ (2 * h + 2)‖ ≤
      ((1 / Y) ^ 2 * (2 * Real.pi * D + Real.pi * D ^ 2) +
        4 * H ^ 2 * volume.real Ω) * (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  let v : ℍ → ℍ := fun z => translate (u z) j
  have hv : Measurable v := (translate_continuous j).measurable.comp hu
  have hdet' : (a + j * c) * d - (b + j * d) * c ≠ 0 := by
    convert hdet using 1
    ring
  have him (z : ℍ) : (v z).im = (u z).im := by
    simp only [v, translate, UpperHalfPlane.im, Complex.add_im, Complex.intCast_im, add_zero]
  have hf : ∀ z ∈ Ω, (v z : ℂ) =
      (((a + j * c : ℤ) : ℂ) * (z : ℂ) + (b + j * d : ℤ)) / ((c : ℂ) * (z : ℂ) + d) := by
    intro z hz
    change (u z : ℂ) + (j : ℂ) = _
    rw [hformula z hz]
    apply (eq_div_iff (hden z hz)).mpr
    rw [add_mul, div_mul_cancel₀ _ (hden z hz)]
    push_cast
    ring
  have hb := integral_matrix_branch_integral_bound (a + j * c) (b + j * d) c d
    hdet' hne v hv Ω hΩ hfinite (fun z => star (coeff z))
    (fun z hz => by simpa only [norm_star] using hcoeff z hz) hD hY hH hlower
    (fun z hz => by simpa only [him] using hupper z hz) hden hbound hf
    (h + 1) (by omega) (by simpa only [Nat.cast_add, Nat.cast_one] using hsmall)
  have hrev := integral_base_reverse_norm (volume.restrict Ω) id v coeff (2 * h + 2)
  simp only [id_eq] at hrev
  change ‖∫ z in Ω, coeff z * base (v z) z ^ (2 * h + 2)‖ ≤ _
  rw [hrev]
  simpa only [Nat.cast_add, Nat.cast_one, show 2 * (h + 1) = 2 * h + 2 by omega] using hb

def branchIntegralError (D Y H area : ℝ) (h : ℕ) : ℝ :=
  ((1 / Y) ^ 2 * (2 * Real.pi * D + Real.pi * D ^ 2) + 4 * H ^ 2 * area) *
    (h + 1 : ℝ) ^ (-(1 / 3 : ℝ))

def periodizedBranchError (D Y H R area : ℝ) (h count : ℕ) : ℝ :=
  (count : ℝ) * branchIntegralError D Y H area h +
    ((1 / 2 : ℝ) ^ (2 * h) * compactKernelBound Y H R) * area

/-- An actual infinite-periodization branch integral with a fully
explicit weight-dependent error.  Arithmetic nonreturn is checked on
the finitely many translated matrices; the infinite tail is proved
analytically. -/
theorem periodized_integral_matrix_branch_bound
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (u : ℍ → ℍ) (hu : Measurable u) (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (coeff : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ 1)
    {D Y H R : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (hregion : ∀ z ∈ Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧
      z.im ≤ H ∧ |(u z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    ‖∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2))‖ ≤
      periodizedBranchError D Y H R (volume.real Ω) h S.card := by
  classical
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ 1 :=
    (ae_restrict_mem hΩ).mono fun z hz => hcoeff z hz
  have hreg : ∀ᵐ z ∂volume.restrict Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧
      z.im ≤ H ∧ |(u z).re - z.re| ≤ R :=
    (ae_restrict_mem hΩ).mono fun z hz => hregion z hz
  have htail := periodization_integral_truncation_bound (volume.restrict Ω) u id hu measurable_id
    coeff hcmeas hc h hY hreg S hfar
  simp only [id_eq, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at htail
  have hint (j : ℤ) : Integrable (fun z => coeff z * base (translate (u z) j) z ^ (2 * h + 2))
      (volume.restrict Ω) := by
    have hm : AEStronglyMeasurable (fun z => coeff z * base (translate (u z) j) z ^ (2 * h + 2))
        (volume.restrict Ω) := hcmeas.mul ((base_continuous.measurable.comp
        (((translate_continuous j).measurable.comp hu).prodMk measurable_id)).pow_const (2 * h + 2)).aestronglyMeasurable
    apply Integrable.of_bound hm 1
    filter_upwards [hc] with z hcz
    rw [norm_mul, norm_pow]
    have hp := pow_le_one₀ (norm_nonneg _) (norm_base_le_one (translate (u z) j) z) (n := 2 * h + 2)
    exact (mul_le_mul_of_nonneg_right hcz (by positivity)).trans (by simpa using hp)
  have hnear : ‖∫ z in Ω, coeff z * (∑ j ∈ S, base (translate (u z) j) z ^ (2 * h + 2))‖ ≤
      (S.card : ℝ) * branchIntegralError D Y H (volume.real Ω) h := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum S (fun j _ => hint j)]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ S, branchIntegralError D Y H (volume.real Ω) h := by
        apply Finset.sum_le_sum
        intro j hj
        apply translated_branch_integral_bound a b c d j hdet (hne j hj) u hu Ω hΩ hfinite
          coeff hcoeff hD hY hH (fun z hz => (hregion z hz).2.1) ?_ hden hbound hformula h hsmall
        intro z hz
        have hx := hregion z hz
        exact (mul_le_mul hx.2.2.2.1 hx.2.2.1 (u z).im_pos.le hH.le).trans_eq (by ring)
      _ = _ := by simp
  have hh := norm_le_norm_sub_add
    (∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2)))
    (∫ z in Ω, coeff z * (∑ j ∈ S, base (translate (u z) j) z ^ (2 * h + 2)))
  exact hh.trans ((add_le_add htail hnear).trans_eq (by unfold periodizedBranchError Measure.real; ring))

theorem periodized_integral_matrix_branch_bound_of_cap
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (u : ℍ → ℍ) (hu : Measurable u) (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (coeff : ℍ → ℂ) {C : ℝ} (hC : 0 < C)
    (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ C)
    {D Y H R : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (hregion : ∀ z ∈ Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧
      z.im ≤ H ∧ |(u z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    ‖∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2))‖ ≤
      C * periodizedBranchError D Y H R (volume.real Ω) h S.card := by
  let c0 : ℍ → ℂ := fun z => (C : ℂ)⁻¹ * coeff z
  have hc0meas : AEStronglyMeasurable c0 (volume.restrict Ω) := aestronglyMeasurable_const.mul hcmeas
  have hc0 : ∀ z ∈ Ω, ‖c0 z‖ ≤ 1 := by
    intro z hz
    dsimp [c0]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    exact (mul_le_mul_of_nonneg_left (hcoeff z hz) (inv_nonneg.mpr hC.le)).trans_eq
      (inv_mul_cancel₀ hC.ne')
  have hb := periodized_integral_matrix_branch_bound a b c d hdet u hu Ω hΩ hfinite
    c0 hc0meas hc0 hD hY hH hregion hden hbound hformula h hsmall S hne hfar
  have he (z : ℍ) : coeff z = (C : ℂ) * c0 z := by
    dsimp [c0]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hC.ne'), one_mul]
  have hi : (∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2))) =
      (C : ℂ) * ∫ z in Ω, c0 z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [he]
    ring
  rw [hi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact mul_le_mul_of_nonneg_left hb hC.le

/-- Quantitative trace decay for the actual Fourier compression.
The only operator hypothesis is its literal action on the lifted
Fourier modes, exactly as in the established trace identity. -/
theorem normalized_matrix_branch_trace_bound
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (u : ℍ → ℍ) (hu : Measurable u) (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (hstrip : Ω ⊆ AsymptoticMassTransport.strip)
    (coeff : ℍ → ℂ) (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ 1)
    {D Y H R ε : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ z ∈ Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧
      z.im ≤ H ∧ |(u z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] Ω.indicator
      (fun z => coeff z * (u z).im * AsymptoticUnweightedKernel.unitRepresentative
        (2 * h) 0 n ε (AsymptoticStripCoordinates.cylinder (u z)))) :
    |liftedTrace h hε W / ((2 * h + 2 : ℕ) : ℝ)| ≤
      periodizedBranchError D Y H R (volume.real Ω) h S.card / (4 * Real.pi) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ 1 :=
    (ae_restrict_mem hΩ).mono fun z hz => hcoeff z hz
  have hreg : ∀ᵐ z ∂volume.restrict Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧ z.im ≤ H :=
    (ae_restrict_mem hΩ).mono fun z hz =>
      ⟨(hregion z hz).1, (hregion z hz).2.1, (hregion z hz).2.2.1, (hregion z hz).2.2.2.1⟩
  have hi := periodized_integral_matrix_branch_bound a b c d hdet u hu Ω hΩ hfinite
    coeff hcmeas hcoeff hD hY hH hregion hden hbound hformula h hsmall S hne hfar
  rw [branch_trace_periodized h hε hY (by norm_num : (0 : ℝ) ≤ 1)
    W Ω hΩ hstrip u hu coeff hcmeas hc hreg hact]
  let I : ℂ := ∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2))
  let p : ℝ := (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi)) / ((2 * h + 2 : ℕ) : ℝ)
  have hp := normalized_trace_prefactor_bound h
  change |(((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ)| ≤ _
  rw [show (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) = p * I.re by dsimp [p]; ring]
  rw [abs_mul, abs_of_nonneg hp.1]
  have hnonneg : 0 ≤ periodizedBranchError D Y H R (volume.real Ω) h S.card := (norm_nonneg I).trans hi
  calc
    p * |I.re| ≤ p * ‖I‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm I) hp.1
    _ ≤ p * periodizedBranchError D Y H R (volume.real Ω) h S.card := mul_le_mul_of_nonneg_left hi hp.1
    _ ≤ (1 / (4 * Real.pi)) * periodizedBranchError D Y H R (volume.real Ω) h S.card :=
      mul_le_mul_of_nonneg_right hp.2 hnonneg
    _ = _ := by ring

theorem normalized_matrix_branch_trace_bound_of_cap
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (u : ℍ → ℍ) (hu : Measurable u) (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (hstrip : Ω ⊆ AsymptoticMassTransport.strip)
    (coeff : ℍ → ℂ) {C : ℝ} (hC : 0 < C) (hcmeas : AEStronglyMeasurable coeff (volume.restrict Ω))
    (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ C)
    {D Y H R ε : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ z ∈ Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧
      z.im ≤ H ∧ |(u z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] Ω.indicator
      (fun z => coeff z * (u z).im * AsymptoticUnweightedKernel.unitRepresentative
        (2 * h) 0 n ε (AsymptoticStripCoordinates.cylinder (u z)))) :
    |liftedTrace h hε W / ((2 * h + 2 : ℕ) : ℝ)| ≤
      (C * periodizedBranchError D Y H R (volume.real Ω) h S.card) / (4 * Real.pi) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ C :=
    (ae_restrict_mem hΩ).mono fun z hz => hcoeff z hz
  have hreg : ∀ᵐ z ∂volume.restrict Ω, Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧ z.im ≤ H :=
    (ae_restrict_mem hΩ).mono fun z hz =>
      ⟨(hregion z hz).1, (hregion z hz).2.1, (hregion z hz).2.2.1, (hregion z hz).2.2.2.1⟩
  have hi := periodized_integral_matrix_branch_bound_of_cap a b c d hdet u hu Ω hΩ hfinite
    coeff hC hcmeas hcoeff hD hY hH hregion hden hbound hformula h hsmall S hne hfar
  rw [branch_trace_periodized h hε hY hC.le
    W Ω hΩ hstrip u hu coeff hcmeas hc hreg hact]
  let I : ℂ := ∫ z in Ω, coeff z * (∑' n : ℤ, base (translate (u z) n) z ^ (2 * h + 2))
  let p : ℝ := (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi)) / ((2 * h + 2 : ℕ) : ℝ)
  have hp := normalized_trace_prefactor_bound h
  change |(((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ)| ≤ _
  rw [show (((2 * h + 1 : ℕ) : ℝ) / (4 * Real.pi) * I.re) / ((2 * h + 2 : ℕ) : ℝ) = p * I.re by dsimp [p]; ring]
  rw [abs_mul, abs_of_nonneg hp.1]
  have hnonneg : 0 ≤ (C * periodizedBranchError D Y H R (volume.real Ω) h S.card) := (norm_nonneg I).trans hi
  calc
    p * |I.re| ≤ p * ‖I‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm I) hp.1
    _ ≤ p * (C * periodizedBranchError D Y H R (volume.real Ω) h S.card) := mul_le_mul_of_nonneg_left hi hp.1
    _ ≤ (1 / (4 * Real.pi)) * (C * periodizedBranchError D Y H R (volume.real Ω) h S.card) :=
      mul_le_mul_of_nonneg_right hp.2 hnonneg
    _ = _ := by ring

#print axioms conj_base
#print axioms integral_base_reverse_norm
#print axioms normalized_trace_prefactor_bound
#print axioms translated_branch_integral_bound
#print axioms periodized_integral_matrix_branch_bound
#print axioms normalized_matrix_branch_trace_bound_of_cap
#print axioms normalized_matrix_branch_trace_bound

end QuantitativeHolomorphic
