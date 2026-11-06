module

public import FinitenessStripDecayV1
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

set_option autoImplicit false

namespace FinitenessContourShift

open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable def horizontal (F : ℂ → ℂ) (a b t : ℝ) : ℂ :=
  ∫ x : ℝ in a..b, F ((x : ℂ)+(t : ℂ)*I)

theorem horizontal_bound {F : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C/(1+z.im^2)) (t : ℝ) :
    ‖horizontal F a b t‖ ≤ (C/(1+t^2))*|b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hab] at hx
  simpa using hF ((x : ℂ)+(t : ℂ)*I) (by simpa using hx.1.le) (by simpa using hx.2)

theorem majorant_zero (C L : ℝ) :
    Tendsto (fun t : ℝ => (C/(1+t^2))*L) atTop (𝓝 0) := by
  have hd : Tendsto (fun t : ℝ => 1+t^2) atTop atTop :=
    tendsto_atTop_mono (fun t : ℝ => by linarith : ∀ t : ℝ, t^2 ≤ 1+t^2)
      (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  simpa only [zero_mul] using (Filter.Tendsto.const_div_atTop hd C).mul_const L

theorem horizontal_zero {F : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C/(1+z.im^2)) :
    Tendsto (horizontal F a b) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => horizontal F a b (-t)) atTop (𝓝 0) := by
  constructor
  · exact squeeze_zero_norm (horizontal_bound hab hF) (majorant_zero C |b-a|)
  · apply squeeze_zero_norm _ (majorant_zero C |b-a|)
    intro t
    simpa only [neg_sq] using horizontal_bound hab hF (-t)

/-- Contour shifting across an entire strip, with horizontal edges killed
by a proved Cauchy majorant and absolutely convergent vertical integrals. -/
theorem vertical_eq {F : ℂ → ℂ} (hhol : Differentiable ℂ F) {a b C : ℝ} (hab : a ≤ b)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C/(1+z.im^2))
    (hia : VerticalIntegrable F a) (hib : VerticalIntegrable F b) :
    (∫ t : ℝ, F ((a : ℂ)+(t : ℂ)*I)) = ∫ t : ℝ, F ((b : ℂ)+(t : ℂ)*I) := by
  let V (x T : ℝ) : ℂ := ∫ t : ℝ in -T..T, F ((x : ℂ)+(t : ℂ)*I)
  have hva : Tendsto (V a) atTop (𝓝 (∫ t : ℝ, F ((a : ℂ)+(t : ℂ)*I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (V b) atTop (𝓝 (∫ t : ℝ, F ((b : ℂ)+(t : ℂ)*I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  obtain ⟨hu,hd⟩ := horizontal_zero hab hF
  have he (T : ℝ) : horizontal F a b (-T)-horizontal F a b T+I*V b T-I*V a T=0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ)+((-T : ℝ) : ℂ)*I) ((b : ℂ)+(T : ℂ)*I) hhol.differentiableOn
    simpa [horizontal, V, smul_eq_mul] using hh
  have hl := ((hd.sub hu).add (hvb.const_mul I)).sub (hva.const_mul I)
  have hz : Tendsto (fun T : ℝ => horizontal F a b (-T)-horizontal F a b T+I*V b T-I*V a T)
      atTop (𝓝 0) := by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  have hh := tendsto_nhds_unique hl hz
  simp only [sub_self, zero_add] at hh
  have hm : I*((∫ t : ℝ, F ((b : ℂ)+(t : ℂ)*I))-(∫ t : ℝ, F ((a : ℂ)+(t : ℂ)*I)))=0 := by
    simpa only [mul_sub] using hh
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left I_ne_zero)).symm

#print axioms horizontal_zero
#print axioms vertical_eq

end FinitenessContourShift
