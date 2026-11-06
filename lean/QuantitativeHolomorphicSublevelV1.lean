module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory Set

/-- A quadratic sublevel set is covered by two disks, without any
separation hypothesis on its roots. -/
theorem factored_sublevel_subset (a u v : ℂ) (ha : 1 ≤ ‖a‖)
    {r : ℝ} (hr : 0 ≤ r) :
    {z : ℂ | ‖a * (z - u) * (z - v)‖ < r} ⊆
      Metric.ball u (Real.sqrt r) ∪ Metric.ball v (Real.sqrt r) := by
  intro z hz
  by_contra hn
  simp only [mem_union, Metric.mem_ball, dist_eq_norm, not_or, not_lt] at hn
  have hprod : r ≤ ‖z - u‖ * ‖z - v‖ := by
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r,
      mul_le_mul hn.1 hn.2 (Real.sqrt_nonneg r) (norm_nonneg (z - u))]
  have ha' : ‖z - u‖ * ‖z - v‖ ≤ ‖a‖ * ‖z - u‖ * ‖z - v‖ := by
    nlinarith [mul_nonneg (norm_nonneg (z - u)) (norm_nonneg (z - v))]
  simp only [mem_ofPred_eq, norm_mul] at hz
  linarith

theorem factored_sublevel_volume (a u v : ℂ) (ha : 1 ≤ ‖a‖)
    {r : ℝ} (hr : 0 ≤ r) :
    volume {z : ℂ | ‖a * (z - u) * (z - v)‖ < r} ≤
      ENNReal.ofReal (2 * Real.pi * r) := by
  calc
    _ ≤ volume (Metric.ball u (Real.sqrt r) ∪ Metric.ball v (Real.sqrt r)) :=
      measure_mono (factored_sublevel_subset a u v ha hr)
    _ ≤ volume (Metric.ball u (Real.sqrt r)) +
        volume (Metric.ball v (Real.sqrt r)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * Real.pi * r) := by
      rw [Complex.volume_ball, Complex.volume_ball]
      have hsq : ENNReal.ofReal (Real.sqrt r) ^ 2 = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]
      rw [hsq]
      have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      rw [hpi, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

theorem complex_quadratic_factorization (a b c : ℂ) (ha : a ≠ 0) :
    ∃ u v : ℂ, ∀ z : ℂ, a * z ^ 2 + b * z + c = a * (z - u) * (z - v) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 4 * a * c) (by decide : 0 < 2)
  refine ⟨(-b + s) / (2 * a), (-b - s) / (2 * a), ?_⟩
  intro z
  field_simp [ha]
  linear_combination hs

/-- Uniform area bound for every complex quadratic whose leading
coefficient has norm at least one; in particular this applies to any
nonzero integral leading coefficient. -/
theorem quadratic_sublevel_volume (a b c : ℂ) (ha : 1 ≤ ‖a‖)
    {r : ℝ} (hr : 0 ≤ r) :
    volume {z : ℂ | ‖a * z ^ 2 + b * z + c‖ < r} ≤
      ENNReal.ofReal (2 * Real.pi * r) := by
  have hane : a ≠ 0 := by intro h; norm_num [h] at ha
  obtain ⟨u, v, huv⟩ := complex_quadratic_factorization a b c hane
  simp_rw [huv]
  exact factored_sublevel_volume a u v ha hr

theorem linear_sublevel_volume (b c : ℂ) (hb : 1 ≤ ‖b‖)
    {r : ℝ} (hr : 0 ≤ r) :
    volume {z : ℂ | ‖b * z + c‖ < r} ≤ ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hb0 : b ≠ 0 := by intro h; norm_num [h] at hb
  have hsub : {z : ℂ | ‖b * z + c‖ < r} ⊆ Metric.ball (-c / b) r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have he : b * (z - -c / b) = b * z + c := by field_simp; ring
    have hn := norm_mul b (z - -c / b)
    rw [he] at hn
    have hh : ‖z - -c / b‖ ≤ ‖b‖ * ‖z - -c / b‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hb
    exact hh.trans_lt (by rw [← hn]; exact hz)
  calc
    _ ≤ volume (Metric.ball (-c / b) r) := measure_mono hsub
    _ = ENNReal.ofReal (Real.pi * r ^ 2) := by
      rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr]
      have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      rw [hpi, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The displacement numerator of a rational fractional-linear map.
The denominator is kept explicit because its bound is supplied by the
observation rectangle. -/
theorem fractional_displacement_identity (a b c d z : ℂ) (hden : c * z + d ≠ 0) :
    (z - (a * z + b) / (c * z + d)) * (c * z + d) =
      c * z ^ 2 + (d - a) * z - b := by
  rw [sub_mul, div_mul_cancel₀ _ hden]
  ring

theorem fractional_displacement_quadratic_volume
    (a b c d : ℂ) (hc : 1 ≤ ‖c‖) (Ω : Set ℂ)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 0 < r)
    (hden : ∀ z ∈ Ω, c * z + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖c * z + d‖ ≤ D) :
    volume {z ∈ Ω | ‖z - (a * z + b) / (c * z + d)‖ < r} ≤
      ENNReal.ofReal (2 * Real.pi * D * r) := by
  have hsub : {z ∈ Ω | ‖z - (a * z + b) / (c * z + d)‖ < r} ⊆
      {z | ‖c * z ^ 2 + (d - a) * z + -b‖ < D * r} := by
    intro z hz
    have hdpos : 0 < ‖c * z + d‖ := norm_pos_iff.mpr (hden z hz.1)
    have he := congrArg norm (fractional_displacement_identity a b c d z (hden z hz.1))
    rw [norm_mul] at he
    change ‖c * z ^ 2 + (d - a) * z + -b‖ < D * r
    rw [← sub_eq_add_neg, ← he]
    calc
      _ < r * ‖c * z + d‖ := mul_lt_mul_of_pos_right hz.2 hdpos
      _ ≤ r * D := mul_le_mul_of_nonneg_left (hbound z hz.1) hr.le
      _ = D * r := mul_comm _ _
  calc
    _ ≤ volume {z : ℂ | ‖c * z ^ 2 + (d - a) * z + -b‖ < D * r} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.pi * (D * r)) :=
      quadratic_sublevel_volume c (d - a) (-b) hc (mul_nonneg hD hr.le)
    _ = _ := by congr 1; ring

theorem affine_displacement_linear_volume
    (a b d : ℂ) (ha : 1 ≤ ‖d - a‖) (hd : d ≠ 0)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hbound : ‖d‖ ≤ D) :
    volume {z : ℂ | ‖z - (a * z + b) / d‖ < r} ≤
      ENNReal.ofReal (Real.pi * D ^ 2 * r) := by
  have hsub : {z : ℂ | ‖z - (a * z + b) / d‖ < r} ⊆
      {z | ‖(d - a) * z + -b‖ < D * r} := by
    intro z hz
    have he : (z - (a * z + b) / d) * d = (d - a) * z + -b := by
      rw [sub_mul, div_mul_cancel₀ _ hd]
      ring
    have hen := congrArg norm he
    rw [norm_mul] at hen
    change ‖(d - a) * z + -b‖ < D * r
    rw [← hen]
    calc
      _ < r * ‖d‖ := mul_lt_mul_of_pos_right hz (norm_pos_iff.mpr hd)
      _ ≤ r * D := mul_le_mul_of_nonneg_left hbound hr
      _ = _ := mul_comm _ _
  calc
    _ ≤ volume {z : ℂ | ‖(d - a) * z + -b‖ < D * r} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.pi * (D * r) ^ 2) :=
      linear_sublevel_volume (d - a) (-b) ha (mul_nonneg hD hr)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hrr : r ^ 2 ≤ r := by nlinarith
      calc
        Real.pi * (D * r) ^ 2 = (Real.pi * D ^ 2) * r ^ 2 := by ring
        _ ≤ (Real.pi * D ^ 2) * r := mul_le_mul_of_nonneg_left hrr (by positivity)

theorem translation_displacement_sublevel_empty
    (b d : ℂ) (hb : 1 ≤ ‖b‖) (hd : d ≠ 0)
    {D r : ℝ} (hr : 0 ≤ r) (hbound : ‖d‖ ≤ D) (hsmall : r * D ≤ 1) :
    {z : ℂ | ‖z - (d * z + b) / d‖ < r} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he : (z - (d * z + b) / d) * d = -b := by
    rw [sub_mul, div_mul_cancel₀ _ hd]
    ring
  have hen := congrArg norm he
  rw [norm_mul, norm_neg] at hen
  have hh : ‖b‖ < 1 := calc
    ‖b‖ = ‖z - (d * z + b) / d‖ * ‖d‖ := hen.symm
    _ < r * ‖d‖ := mul_lt_mul_of_pos_right hz (norm_pos_iff.mpr hd)
    _ ≤ r * D := mul_le_mul_of_nonneg_left hbound hr
    _ ≤ 1 := hsmall
  exact (not_lt_of_ge hb) hh

theorem int_complex_norm_ge_one (m : ℤ) (hm : m ≠ 0) : 1 ≤ ‖(m : ℂ)‖ := by
  rw [Complex.norm_intCast]
  have hh : (1 : ℤ) ≤ |m| := by
    have hp : 0 < |m| := abs_pos.mpr hm
    omega
  exact_mod_cast hh

/-- All nonidentity integral matrix branches, including affine maps
and translations.  The two small-radius conditions are explicit.
The bound is polynomial in the denominator bound and is independent
of root separation and of the determinant. -/
theorem integral_matrix_displacement_volume
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (hne : c ≠ 0 ∨ d ≠ a ∨ b ≠ 0) (Ω : Set ℂ)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : r * D ≤ 1)
    (hden : ∀ z ∈ Ω, (c : ℂ) * z + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * z + d‖ ≤ D) :
    volume {z ∈ Ω | ‖z - ((a : ℂ) * z + b) / ((c : ℂ) * z + d)‖ < r} ≤
      ENNReal.ofReal ((2 * Real.pi * D + Real.pi * D ^ 2) * r) := by
  by_cases hc : c ≠ 0
  · apply (fractional_displacement_quadratic_volume a b c d
      (int_complex_norm_ge_one c hc) Ω hD hr hden hbound).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg (by positivity : 0 ≤ Real.pi * D ^ 2) hr.le]
  · have hc0 : c = 0 := not_ne_iff.mp hc
    have hd : (d : ℂ) ≠ 0 := by
      have hdZ : d ≠ 0 := by intro hh; simp [hc0, hh] at hdet
      exact_mod_cast hdZ
    by_cases hΩ : Ω = ∅
    · simp [hΩ]
    · obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hΩ
      have hdD : ‖(d : ℂ)‖ ≤ D := by simpa [hc0] using hbound z₀ hz₀
      by_cases hda : d ≠ a
      · have hda' : 1 ≤ ‖(d : ℂ) - a‖ := by
          exact_mod_cast int_complex_norm_ge_one (d - a) (sub_ne_zero.mpr hda)
        have hh := affine_displacement_linear_volume a b d hda' hd hD hr.le hr1 hdD
        have hsub : {z ∈ Ω | ‖z - ((a : ℂ) * z + b) / ((c : ℂ) * z + d)‖ < r} ⊆
            {z : ℂ | ‖z - ((a : ℂ) * z + b) / d‖ < r} := by
          intro z hz
          simpa [hc0] using hz.2
        apply ((measure_mono hsub).trans hh).trans
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * Real.pi * D) hr.le]
      · have hda0 : d = a := not_ne_iff.mp hda
        have hb : b ≠ 0 := hne.resolve_left hc |>.resolve_left hda
        have hh := translation_displacement_sublevel_empty b d
          (int_complex_norm_ge_one b hb) hd hr.le hdD hsmall
        have he : {z ∈ Ω | ‖z - ((a : ℂ) * z + b) / ((c : ℂ) * z + d)‖ < r} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hz' : z ∈ {z : ℂ | ‖z - ((d : ℂ) * z + b) / d‖ < r} := by
            simpa [hc0, hda0] using hz.2
          simp only [hh, mem_empty_iff_false] at hz'
        rw [he, measure_empty]
        exact bot_le

#print axioms quadratic_sublevel_volume
#print axioms fractional_displacement_quadratic_volume
#print axioms affine_displacement_linear_volume
#print axioms translation_displacement_sublevel_empty
#print axioms integral_matrix_displacement_volume

end QuantitativeHolomorphic
