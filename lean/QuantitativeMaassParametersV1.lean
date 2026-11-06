module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- The slow scale in the shrinking-window theorem. -/
noncomputable def slowScale (t : ℝ) : ℝ := Real.log (Real.log (Real.log t))

/-- Propagation radius chosen from the window width and slow scale. -/
noncomputable def propagation (L ε : ℝ) : ℝ := Real.sqrt (L / ε)

theorem slowScale_tendsto : Tendsto slowScale atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

theorem propagation_mul_width {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    propagation L ε * ε = Real.sqrt (ε * L) := by
  have hp : 0 ≤ propagation L ε * ε := mul_nonneg (Real.sqrt_nonneg _) hε.le
  have hs : (propagation L ε * ε) ^ 2 = ε * L := by
    rw [mul_pow, propagation, Real.sq_sqrt (div_nonneg hL.le hε.le)]
    field_simp
  nlinarith [Real.sq_sqrt (mul_nonneg hε.le hL.le), Real.sqrt_nonneg (ε * L)]

theorem propagation_div_scale {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    propagation L ε / L = (Real.sqrt (ε * L))⁻¹ := by
  have hmul := propagation_mul_width hL hε
  have hs := Real.sq_sqrt (mul_nonneg hε.le hL.le)
  have hroot : 0 < Real.sqrt (ε * L) := Real.sqrt_pos.2 (mul_pos hε hL)
  rw [← one_div (Real.sqrt (ε * L))]
  apply (eq_div_iff hroot.ne').2
  rw [div_mul_eq_mul_div]
  apply (div_eq_one_iff_eq hL.ne').2
  apply mul_left_cancel₀ hε.ne'
  calc
    ε * (propagation L ε * Real.sqrt (ε * L)) =
        (propagation L ε * ε) * Real.sqrt (ε * L) := by ring
    _ = Real.sqrt (ε * L) * Real.sqrt (ε * L) := by rw [hmul]
    _ = ε * L := by nlinarith

/-- The radius simultaneously has negligible relative propagation cost and
resolves the shrinking interval. The only input is ε L → ∞. -/
theorem propagation_limits {α : Type*} {l : Filter α} (L ε : α → ℝ)
    (hL : ∀ᶠ t in l, 0 < L t) (hε : ∀ᶠ t in l, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * L t) l atTop) :
    Tendsto (fun t => propagation (L t) (ε t) / L t) l (𝓝 0) ∧
    Tendsto (fun t => propagation (L t) (ε t) * ε t) l atTop := by
  have hs := Real.tendsto_sqrt_atTop.comp hproduct
  constructor
  · apply (tendsto_inv_atTop_zero.comp hs).congr'
    filter_upwards [hL, hε] with t ht he
    exact (propagation_div_scale ht he).symm
  · apply hs.congr'
    filter_upwards [hL, hε] with t ht he
    exact (propagation_mul_width ht he).symm

/-- Exponential propagation losses are absorbed by any fixed positive
exponential saving in the slow scale, even after division by ε. -/
theorem propagation_excess_tendsto {α : Type*} {l : Filter α}
    (L ε R : α → ℝ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hL : Tendsto L l atTop) (hε : ∀ᶠ t in l, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * L t) l atTop)
    (hR : Tendsto (fun t => R t / L t) l (𝓝 0)) :
    Tendsto (fun t => Real.exp (C * R t - c * L t) / ε t) l (𝓝 0) := by
  have hhalf : 0 < c / (2 * (C + 1)) := by positivity
  have hsmall : ∀ᶠ t in l, R t / L t < c / (2 * (C + 1)) :=
    hR.eventually (gt_mem_nhds hhalf)
  have hmajor : Tendsto (fun t => L t * Real.exp (-(c / 2) * L t)) l (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (c / 2)
      (by positivity : 0 < c / 2)).comp hL
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε, hL.eventually (eventually_gt_atTop (0 : ℝ)),
      hproduct.eventually (eventually_ge_atTop (1 : ℝ)), hsmall] with t he hl hp hr
    have hr' : R t < c / (2 * (C + 1)) * L t := (div_lt_iff₀ hl).1 hr
    have hratio : C * (c / (2 * (C + 1))) ≤ c / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (C + 1))).2
      nlinarith
    have hexp : C * R t - c * L t ≤ -(c / 2) * L t := by
      have h₁ := mul_le_mul_of_nonneg_left hr'.le hC
      have h₂ := mul_le_mul_of_nonneg_right hratio hl.le
      nlinarith
    have hinv : 1 / ε t ≤ L t := (div_le_iff₀ he).2 (by nlinarith)
    calc
      _ ≤ Real.exp (-(c / 2) * L t) / ε t :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) he.le
      _ ≤ L t * Real.exp (-(c / 2) * L t) := by
        have hh := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (-(c / 2) * L t)).le
        simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hh

theorem chosen_propagation_excess {α : Type*} {l : Filter α}
    (L ε : α → ℝ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hL : Tendsto L l atTop) (hε : ∀ᶠ t in l, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * L t) l atTop) :
    Tendsto (fun t => Real.exp (C * propagation (L t) (ε t) - c * L t) / ε t)
      l (𝓝 0) := by
  exact propagation_excess_tendsto L ε (fun t => propagation (L t) (ε t)) C c
    hC hc hL hε hproduct
    (propagation_limits L ε (hL.eventually (eventually_gt_atTop (0 : ℝ))) hε hproduct).1

/-- The smoothing width used for the positive bandlimited window. -/
noncomputable def smoothingWidth (L ε : ℝ) : ℝ :=
  Real.sqrt (ε / propagation L ε)

theorem smoothingWidth_limits {α : Type*} {l : Filter α}
    (L ε : α → ℝ) (hL : ∀ᶠ t in l, 0 < L t)
    (hε : ∀ᶠ t in l, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * L t) l atTop) :
    Tendsto (fun t => smoothingWidth (L t) (ε t) / ε t) l (𝓝 0) ∧
    Tendsto (fun t => smoothingWidth (L t) (ε t) * propagation (L t) (ε t))
      l atTop := by
  have hR : ∀ᶠ t in l, 0 < propagation (L t) (ε t) := by
    filter_upwards [hL, hε] with t ht he
    exact Real.sqrt_pos.2 (div_pos ht he)
  exact propagation_limits ε (fun t => propagation (L t) (ε t)) hε hR
    (propagation_limits L ε hL hε hproduct).2

/-- Specialization to the literal triple-logarithmic scale; no regularity
or monotonicity assumption on the window width is required. -/
theorem shrinking_window_parameters (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => propagation (slowScale t) (ε t) / slowScale t)
      atTop (𝓝 0) ∧
    Tendsto (fun t => propagation (slowScale t) (ε t) * ε t) atTop atTop ∧
    Tendsto (fun t => smoothingWidth (slowScale t) (ε t) / ε t) atTop (𝓝 0) ∧
    Tendsto (fun t => smoothingWidth (slowScale t) (ε t) *
      propagation (slowScale t) (ε t)) atTop atTop := by
  have hL := slowScale_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  exact ⟨(propagation_limits slowScale ε hL hε hproduct).1,
    (propagation_limits slowScale ε hL hε hproduct).2,
    smoothingWidth_limits slowScale ε hL hε hproduct⟩

/-- A concrete admissible shrinking width for deducing the pointwise bound. -/
noncomputable def canonicalWidth (t : ℝ) : ℝ := (Real.sqrt (slowScale t))⁻¹

theorem canonicalWidth_properties :
    (∀ᶠ t in atTop, 0 < canonicalWidth t) ∧
    Tendsto canonicalWidth atTop (𝓝 0) ∧
    Tendsto (fun t => canonicalWidth t * slowScale t) atTop atTop := by
  have hpos := slowScale_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  have hs := Real.tendsto_sqrt_atTop.comp slowScale_tendsto
  refine ⟨?_, tendsto_inv_atTop_zero.comp hs, ?_⟩
  · filter_upwards [hpos] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.2 ht)
  · apply hs.congr'
    filter_upwards [hpos] with t ht
    have hroot : Real.sqrt (slowScale t) ≠ 0 := (Real.sqrt_pos.2 ht).ne'
    have hsq := Real.sq_sqrt ht.le
    dsimp only [canonicalWidth, Function.comp_def]
    field_simp
    nlinarith

#print axioms slowScale_tendsto
#print axioms propagation_mul_width
#print axioms propagation_div_scale
#print axioms propagation_limits
#print axioms propagation_excess_tendsto
#print axioms chosen_propagation_excess
#print axioms smoothingWidth_limits
#print axioms shrinking_window_parameters
#print axioms canonicalWidth_properties

end QuantitativeMaass
