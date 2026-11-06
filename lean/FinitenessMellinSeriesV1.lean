module

public import FinitenessMellinContourV1
public import FinitenessGammaMellinV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option autoImplicit false

namespace FinitenessMellinSeries

open Complex MeasureTheory FinitenessMellinContour

/-- General Dirichlet series in logarithmic frequencies. The ordinary
application has d(n)=log(n+1). -/
noncomputable def series (a : ℕ → ℂ) (d : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n, a n*Complex.exp ((-d n : ℝ)*z)

noncomputable def term (a : ℕ → ℂ) (d : ℕ → ℝ) (σ l : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  a n*kernel Gamma (l+d n) ((σ : ℂ)+(t : ℂ)*I)

theorem term_norm (a : ℕ → ℂ) (d : ℕ → ℝ) (σ l : ℝ) (n : ℕ) (t : ℝ) :
    ‖term a d σ l n t‖ =
      (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))*‖Gamma ((σ : ℂ)+(t : ℂ)*I)‖ := by
  rw [term, norm_mul, kernel_norm]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  rw [show -(l+d n)*σ = -l*σ+(-σ*d n) by ring, Real.exp_add]
  ring

theorem term_integrable {σ : ℝ} (hσ : 0 < σ) (a : ℕ → ℂ) (d : ℕ → ℝ)
    (l : ℝ) (n : ℕ) : Integrable (term a d σ l n) := by
  have hg : Integrable (fun t : ℝ => Gamma ((σ : ℂ)+(t : ℂ)*I)) := by
    simpa only [pow_zero, one_mul] using FinitenessGammaIntegrability.integrable σ hσ 0
  have hc : Continuous (term a d σ l n) := by
    unfold term kernel
    exact continuous_const.mul
      ((Complex.continuous_exp.comp (by fun_prop)).mul
        (FinitenessGammaIntegrability.gamma_continuous σ hσ))
  apply (hg.norm.const_mul (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => le_of_eq (term_norm a d σ l n t))

theorem term_integral_norm (a : ℕ → ℂ) (d : ℕ → ℝ) (σ l : ℝ) (n : ℕ) :
    (∫ t : ℝ, ‖term a d σ l n t‖) =
      (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))*
        (∫ t : ℝ, ‖Gamma ((σ : ℂ)+(t : ℂ)*I)‖) := by
  simp_rw [term_norm]
  exact integral_const_mul _ _

theorem term_integral_norm_summable {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ}
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n))) (l : ℝ) :
    Summable (fun n => ∫ t : ℝ, ‖term a d σ l n t‖) := by
  simp_rw [term_integral_norm]
  exact (ha.mul_left (Real.exp (-l*σ))).mul_right _

theorem kernel_series (a : ℕ → ℂ) (d : ℕ → ℝ) (l : ℝ) (z : ℂ) :
    kernel (fun w => Gamma w*series a d w) l z = ∑' n, a n*kernel Gamma (l+d n) z := by
  simp only [kernel, series]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : ((-(l+d n) : ℝ):ℂ)*z = ((-l : ℝ):ℂ)*z+((-d n : ℝ):ℂ)*z := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- Opening the Dirichlet series under the inverse Mellin integral is
justified by an explicit summable integral-of-norm majorant. -/
theorem exchange {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n))) (l : ℝ) :
    integral (fun w => Gamma w*series a d w) σ l =
      ∑' n, a n*integral Gamma σ (l+d n) := by
  unfold FinitenessMellinContour.integral
  simp_rw [kernel_series]
  have hh := integral_tsum_of_summable_integral_norm (term_integrable hσ a d l)
    (term_integral_norm_summable ha l)
  change (∫ t : ℝ, ∑' n, term a d σ l n t) = _
  rw [← hh]
  apply tsum_congr
  intro n
  exact integral_const_mul _ _

/-- Exact inverse transform of a Gamma-completed Dirichlet series. -/
theorem inverse {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n))) (l : ℝ) :
    mellinInv σ (fun w => Gamma w*series a d w) (Real.exp l) =
      ∑' n, a n*(Real.exp (-Real.exp (l+d n)) : ℂ) := by
  rw [mellinInv_eq (Real.exp_pos l), Real.log_exp, exchange hσ ha,
    Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hh := FinitenessGammaMellin.inverse_gamma hσ (Real.exp_pos (l+d n))
  rw [mellinInv_eq (Real.exp_pos (l+d n)), Real.log_exp, Complex.real_smul] at hh
  calc
    _ = a n*((((1/(2*Real.pi):ℝ):ℂ))*integral Gamma σ (l+d n)) := by ring
    _ = _ := by rw [hh]

#print axioms exchange
#print axioms inverse

end FinitenessMellinSeries
