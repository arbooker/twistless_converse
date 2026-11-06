module

public import FinitenessFiniteOrderV1
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.MellinTransform

@[expose] public section

set_option autoImplicit false

namespace FinitenessStripDecay

open Complex Filter Asymptotics Set MeasureTheory FinitenessFiniteOrder
open scoped Topology

/-- Finite order pays the prior-growth hypothesis of the strip theorem. -/
theorem bounded_strip {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b C : ℝ} (hab : a < b)
    (ha : ∀ z : ℂ, z.re=a → ‖F z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re=b → ‖F z‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖F z‖ ≤ C := by
  have hp : 0 < Real.pi/(b-a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  let c := (Real.pi/(b-a))/2
  have hc : 0 < c := half_pos hp
  have hcsmall : c < Real.pi/(b-a) := by dsimp [c]; linarith
  obtain ⟨B,hB⟩ := strip_double_exp hF (show 0 ≤ |a|+|b| by positivity) hc
  apply PhragmenLindelof.vertical_strip hhol.diffContOnCl _ ha hb hza hzb
  refine ⟨c,hcsmall,B,IsBigO.of_bound 1 ?_⟩
  apply Filter.mem_of_superset (Filter.mem_inf_of_right (Filter.mem_principal_self _))
  intro w hw
  have hw' : a < w.re ∧ w.re < b := hw
  have hwabs : |w.re| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor <;> linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b]
  simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp, one_mul] using hB w hwabs

/-- Boundary polynomial decay becomes uniform decay throughout the strip. -/
theorem weighted_strip {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b : ℝ} (hab : a < b) (n : ℕ) {C : ℝ}
    (ha : ∀ z : ℂ, z.re=a → ‖z‖^n*‖F z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re=b → ‖z‖^n*‖F z‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : |z.im|^n*‖F z‖ ≤ C := by
  have hh : ‖z^n*F z‖ ≤ C := bounded_strip (F := fun w => w^n*F w)
    ((differentiable_id.pow n).mul hhol) (FinitenessFiniteOrder.pow_mul hF n) hab
    (fun w hw => by simpa only [norm_mul, norm_pow] using ha w hw)
    (fun w hw => by simpa only [norm_mul, norm_pow] using hb w hw) hza hzb
  apply le_trans _ hh
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) n) (norm_nonneg _)

theorem cauchy_bound {F : ℂ → ℂ} {a b C₀ C₂ : ℝ}
    (h0 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C₀)
    (h2 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im|^2*‖F z‖ ≤ C₂)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖F z‖ ≤ (C₀+C₂)/(1+z.im^2) := by
  have hh0 := h0 z hza hzb
  have hh2 := h2 z hza hzb
  rw [sq_abs] at hh2
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<1+z.im^2)).mpr
  nlinarith

/-- Every vertical line in such a strip is absolutely integrable. -/
theorem vertical_integrable {F : ℂ → ℂ} (hF : Continuous F) {a b C₀ C₂ : ℝ}
    (h0 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C₀)
    (h2 : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im|^2*‖F z‖ ≤ C₂)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) : VerticalIntegrable F σ := by
  have hc : Continuous (fun t : ℝ => F ((σ : ℂ)+(t : ℂ)*I)) := hF.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (C₀+C₂)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simpa only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, div_eq_mul_inv]
    using cauchy_bound h0 h2 (z := (σ : ℂ)+(t : ℂ)*I)
      (by simpa using hσa) (by simpa using hσb)

#print axioms bounded_strip
#print axioms weighted_strip
#print axioms vertical_integrable

end FinitenessStripDecay
