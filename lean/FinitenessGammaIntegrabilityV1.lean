module

public import FinitenessGammaDecayV1
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

namespace FinitenessGammaIntegrability

open Complex MeasureTheory FinitenessGammaDecay

theorem weighted_cauchy_bound (σ : ℝ) (hσ : 0 < σ) (d : ℕ) (t : ℝ) :
    |t|^d * ‖Gamma ((σ : ℂ)+(t : ℂ)*I)‖ ≤
      (Real.Gamma (σ+(d : ℝ))+Real.Gamma (σ+((d+2 : ℕ) : ℝ))) / (1+t^2) := by
  have h1 := vertical_line σ hσ d t
  have h2 := vertical_line σ hσ (d+2) t
  have he : |t|^(d+2) = |t|^d*t^2 := by rw [pow_add, sq_abs]
  rw [he] at h2
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<1+t^2)).mpr
  nlinarith

theorem gamma_continuous (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => Gamma ((σ : ℂ)+(t : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : ∀ n : ℕ, (σ : ℂ)+(t : ℂ)*I ≠ -(n : ℂ) := by
    intro n he
    have hre := congrArg Complex.re he
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_re, natCast_re] at hre
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hc : ContinuousAt (fun x : ℝ => (σ : ℂ)+(x : ℂ)*I) t := by fun_prop
  exact ContinuousAt.comp (f := fun x : ℝ => (σ : ℂ)+(x : ℂ)*I) (x := t)
    (Complex.continuousAt_Gamma _ hn) hc

/-- Every polynomially weighted Gamma function on a positive vertical line
is absolutely integrable. This pays the vertical decay needed by Mellin
inversion without invoking an unformalized Stirling theorem. -/
theorem integrable (σ : ℝ) (hσ : 0 < σ) (d : ℕ) :
    Integrable (fun t : ℝ => (t : ℂ)^d * Gamma ((σ : ℂ)+(t : ℂ)*I)) := by
  have hc : Continuous (fun t : ℝ => (t : ℂ)^d * Gamma ((σ : ℂ)+(t : ℂ)*I)) :=
    (continuous_ofReal.pow d).mul (gamma_continuous σ hσ)
  apply ((integrable_inv_one_add_sq).const_mul
    (Real.Gamma (σ+(d : ℝ))+Real.Gamma (σ+((d+2 : ℕ) : ℝ)))).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
    using weighted_cauchy_bound σ hσ d t

#print axioms weighted_cauchy_bound
#print axioms integrable

end FinitenessGammaIntegrability
