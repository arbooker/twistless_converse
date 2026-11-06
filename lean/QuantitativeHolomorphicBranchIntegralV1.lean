module

public import QuantitativeHolomorphicKernelIntegralV1
public import QuantitativeHolomorphicHyperbolicSublevelV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory Set UpperHalfPlane AsymptoticBergmanDecay

/-- Quantitative integral decay for a single fractional-linear branch
with nonzero integral-scale lower-left entry.  The coefficient may be
merely bounded; no regularity or cancellation is assumed.  This is a
proved branch estimate, not a hypothesis packaging the trace theorem. -/
theorem fractional_branch_integral_bound
    (a b c d : ℂ) (hc : 1 ≤ ‖c‖) (u : ℍ → ℍ) (hu : Measurable u)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (coeff : ℍ → ℂ) (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ 1)
    {D Y H : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (hlower : ∀ z ∈ Ω, Y ≤ z.im)
    (hupper : ∀ z ∈ Ω, z.im * (u z).im ≤ H ^ 2)
    (hden : ∀ z ∈ Ω, c * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖c * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = (a * (z : ℂ) + b) / (c * (z : ℂ) + d))
    (n : ℕ) (hn : 0 < n) :
    ‖∫ z in Ω, coeff z * base z (u z) ^ (2 * n)‖ ≤
      ((1 / Y) ^ 2 * (2 * Real.pi * D) + 4 * H ^ 2 * volume.real Ω) *
        (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  let r : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  let E : Set ℍ := {z | ‖(z : ℂ) - (u z : ℂ)‖ < r}
  have hE : MeasurableSet E := by
    apply measurableSet_lt _ measurable_const
    exact (measurable_coe.sub (measurable_coe.comp hu)).norm
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hsub : (volume.restrict Ω).real E ≤ ((1 / Y) ^ 2 * (2 * Real.pi * D)) * r := by
    have heq : E ∩ Ω =
        {z ∈ Ω | ‖(z : ℂ) - (a * (z : ℂ) + b) / (c * (z : ℂ) + d)‖ < r} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.2, by simpa only [E, mem_ofPred_eq, ← hformula z hz.2] using hz.1⟩
      · intro hz
        exact ⟨by simpa only [E, mem_ofPred_eq, hformula z hz.1] using hz.2, hz.1⟩
    have hh := hyperbolic_fractional_displacement_quadratic_volume a b c d hc Ω
      hD hr hY hlower hden hbound
    have hh' : volume.restrict Ω E ≤
        ENNReal.ofReal ((1 / Y) ^ 2 * (2 * Real.pi * D * r)) := by
      rw [Measure.restrict_apply hE, heq]
      exact hh
    have hhreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
    rw [ENNReal.toReal_ofReal (by positivity)] at hhreal
    exact hhreal.trans_eq (by ring)
  have hbc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ 1 :=
    (ae_restrict_mem hΩ).mono fun z hz => hcoeff z hz
  have hbu : ∀ᵐ z ∂volume.restrict Ω, z.im * (u z).im ≤ H ^ 2 :=
    (ae_restrict_mem hΩ).mono fun z hz => hupper z hz
  have hb := bergman_integral_of_sublevel_ae (volume.restrict Ω) id u coeff hH hr n
    (inverse_cube_root_identity n hn) hbc hbu hE hsub
  simpa only [id_eq, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.real] using hb

/-- Quantitative integral decay for a single fractional-linear branch
represented by a nonidentity integral matrix.  The coefficient may be
merely bounded; no regularity or cancellation is assumed.  This is a
proved branch estimate, not a hypothesis packaging the trace theorem. -/
theorem integral_matrix_branch_integral_bound
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (hne : c ≠ 0 ∨ d ≠ a ∨ b ≠ 0) (u : ℍ → ℍ) (hu : Measurable u)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (coeff : ℍ → ℂ) (hcoeff : ∀ z ∈ Ω, ‖coeff z‖ ≤ 1)
    {D Y H : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H)
    (hlower : ∀ z ∈ Ω, Y ≤ z.im)
    (hupper : ∀ z ∈ Ω, z.im * (u z).im ≤ H ^ 2)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, (u z : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (n : ℕ) (hn : 0 < n)
    (hsmall : (n : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1) :
    ‖∫ z in Ω, coeff z * base z (u z) ^ (2 * n)‖ ≤
      ((1 / Y) ^ 2 * ((2 * Real.pi * D + Real.pi * D ^ 2)) + 4 * H ^ 2 * volume.real Ω) *
        (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  let r : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (by norm_num)
  let E : Set ℍ := {z | ‖(z : ℂ) - (u z : ℂ)‖ < r}
  have hE : MeasurableSet E := by
    apply measurableSet_lt _ measurable_const
    exact (measurable_coe.sub (measurable_coe.comp hu)).norm
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfinite
  have hsub : (volume.restrict Ω).real E ≤ ((1 / Y) ^ 2 * ((2 * Real.pi * D + Real.pi * D ^ 2))) * r := by
    have heq : E ∩ Ω =
        {z ∈ Ω | ‖(z : ℂ) - ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d)‖ < r} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.2, by simpa only [E, mem_ofPred_eq, ← hformula z hz.2] using hz.1⟩
      · intro hz
        exact ⟨by simpa only [E, mem_ofPred_eq, hformula z hz.1] using hz.2, hz.1⟩
    have hh := hyperbolic_integral_matrix_displacement_volume a b c d hdet hne Ω
      hD hr hr1 hsmall hY hlower hden hbound
    have hh' : volume.restrict Ω E ≤
        ENNReal.ofReal ((1 / Y) ^ 2 * ((2 * Real.pi * D + Real.pi * D ^ 2) * r)) := by
      rw [Measure.restrict_apply hE, heq]
      exact hh
    have hhreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
    rw [ENNReal.toReal_ofReal (by positivity)] at hhreal
    exact hhreal.trans_eq (by ring)
  have hbc : ∀ᵐ z ∂volume.restrict Ω, ‖coeff z‖ ≤ 1 :=
    (ae_restrict_mem hΩ).mono fun z hz => hcoeff z hz
  have hbu : ∀ᵐ z ∂volume.restrict Ω, z.im * (u z).im ≤ H ^ 2 :=
    (ae_restrict_mem hΩ).mono fun z hz => hupper z hz
  have hb := bergman_integral_of_sublevel_ae (volume.restrict Ω) id u coeff hH hr n
    (inverse_cube_root_identity n hn) hbc hbu hE hsub
  simpa only [id_eq, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.real] using hb

#print axioms integral_matrix_branch_integral_bound
#print axioms fractional_branch_integral_bound

end QuantitativeHolomorphic
