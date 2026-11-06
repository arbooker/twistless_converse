module

public import QuantitativeHolomorphicSublevelV1
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory Set UpperHalfPlane

/-- On a region of height at least `Y`, hyperbolic area is at most
`Y⁻²` times its Euclidean image area.  No measurability of the region
is needed. -/
theorem hyperbolic_volume_le_euclidean (E : Set ℍ) {Y : ℝ} (hY : 0 < Y)
    (hheight : ∀ z ∈ E, Y ≤ z.im) :
    volume E ≤ ENNReal.ofReal ((1 / Y) ^ 2) * volume (UpperHalfPlane.coe '' E) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc
    _ ≤ ∫⁻ _ : ℂ in UpperHalfPlane.coe '' E, ENNReal.ofReal ((1 / Y) ^ 2) := by
      apply setLIntegral_mono measurable_const
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      have hbound : (1 / u.im) ^ 2 ≤ (1 / Y) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hY (hheight u hu)) 2
      have he : (↑((1 / ‖(u : ℂ).im‖₊) ^ 2 : NNReal) : ENNReal) =
          ENNReal.ofReal ((1 / u.im) ^ 2) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        simp [Real.nnnorm_of_nonneg u.im_pos.le]
      rw [he]
      exact ENNReal.ofReal_le_ofReal hbound
    _ = _ := by simp

theorem hyperbolic_fractional_displacement_quadratic_volume
    (a b c d : ℂ) (hc : 1 ≤ ‖c‖) (Ω : Set ℍ)
    {D r Y : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hY : 0 < Y)
    (hheight : ∀ z ∈ Ω, Y ≤ z.im)
    (hden : ∀ z ∈ Ω, c * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖c * (z : ℂ) + d‖ ≤ D) :
    volume {z ∈ Ω | ‖(z : ℂ) - (a * (z : ℂ) + b) / (c * (z : ℂ) + d)‖ < r} ≤
      ENNReal.ofReal ((1 / Y) ^ 2 * (2 * Real.pi * D * r)) := by
  let E := {z ∈ Ω | ‖(z : ℂ) - (a * (z : ℂ) + b) / (c * (z : ℂ) + d)‖ < r}
  have hE : ∀ z ∈ E, Y ≤ z.im := fun z hz => hheight z hz.1
  have hsub : UpperHalfPlane.coe '' E ⊆
      {z ∈ UpperHalfPlane.coe '' Ω | ‖z - (a * z + b) / (c * z + d)‖ < r} := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, hu.2⟩
  have hplanar := fractional_displacement_quadratic_volume a b c d hc
    (UpperHalfPlane.coe '' Ω) hD hr ?_ ?_
  · calc
      volume E ≤ ENNReal.ofReal ((1 / Y) ^ 2) * volume (UpperHalfPlane.coe '' E) :=
        hyperbolic_volume_le_euclidean E hY hE
      _ ≤ ENNReal.ofReal ((1 / Y) ^ 2) * ENNReal.ofReal (2 * Real.pi * D * r) :=
        mul_le_mul le_rfl ((measure_mono hsub).trans hplanar) (by positivity) (by positivity)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  · rintro z ⟨u, hu, rfl⟩
    exact hden u hu
  · rintro z ⟨u, hu, rfl⟩
    exact hbound u hu

theorem hyperbolic_integral_matrix_displacement_volume
    (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (hne : c ≠ 0 ∨ d ≠ a ∨ b ≠ 0) (Ω : Set ℍ)
    {D r Y : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : r * D ≤ 1) (hY : 0 < Y)
    (hheight : ∀ z ∈ Ω, Y ≤ z.im)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D) :
    volume {z ∈ Ω | ‖(z : ℂ) - ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d)‖ < r} ≤
      ENNReal.ofReal ((1 / Y) ^ 2 * ((2 * Real.pi * D + Real.pi * D ^ 2) * r)) := by
  let E := {z ∈ Ω | ‖(z : ℂ) - ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d)‖ < r}
  have hE : ∀ z ∈ E, Y ≤ z.im := fun z hz => hheight z hz.1
  have hsub : UpperHalfPlane.coe '' E ⊆
      {z ∈ UpperHalfPlane.coe '' Ω | ‖z - ((a : ℂ) * z + b) / ((c : ℂ) * z + d)‖ < r} := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, hu.2⟩
  have hplanar := integral_matrix_displacement_volume a b c d hdet hne
    (UpperHalfPlane.coe '' Ω) hD hr hr1 hsmall ?_ ?_
  · calc
      volume E ≤ ENNReal.ofReal ((1 / Y) ^ 2) * volume (UpperHalfPlane.coe '' E) :=
        hyperbolic_volume_le_euclidean E hY hE
      _ ≤ ENNReal.ofReal ((1 / Y) ^ 2) * ENNReal.ofReal ((2 * Real.pi * D + Real.pi * D ^ 2) * r) :=
        mul_le_mul le_rfl ((measure_mono hsub).trans hplanar) (by positivity) (by positivity)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  · rintro z ⟨u, hu, rfl⟩
    exact hden u hu
  · rintro z ⟨u, hu, rfl⟩
    exact hbound u hu

#print axioms hyperbolic_integral_matrix_displacement_volume
#print axioms hyperbolic_volume_le_euclidean
#print axioms hyperbolic_fractional_displacement_quadratic_volume

end QuantitativeHolomorphic
