module

public import MaassParityMellinV1
public import FinitenessMellinSeriesV1

set_option autoImplicit false

@[expose] public section

open Complex MeasureTheory FinitenessMellinContour FinitenessMellinSeries

namespace MaassMellinSeries

noncomputable def term (G : ℂ → ℂ) (a : ℕ → ℂ) (d : ℕ → ℝ)
    (σ l : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  a n*kernel G (l+d n) ((σ:ℂ)+(t:ℂ)*I)

theorem term_norm (G : ℂ → ℂ) (a : ℕ → ℂ) (d : ℕ → ℝ) (σ l : ℝ) (n : ℕ) (t : ℝ) :
    ‖term G a d σ l n t‖ =
      (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))*‖G ((σ:ℂ)+(t:ℂ)*I)‖ := by
  rw [term, norm_mul, kernel_norm]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  rw [show -(l+d n)*σ = -l*σ+(-σ*d n) by ring, Real.exp_add]
  ring

theorem term_integrable {G : ℂ → ℂ} {σ : ℝ} (hG : VerticalIntegrable G σ)
    (a : ℕ → ℂ) (d : ℕ → ℝ) (l : ℝ) (n : ℕ) : Integrable (term G a d σ l n) := by
  have hm : AEStronglyMeasurable (term G a d σ l n) := by
    unfold term kernel
    apply AEStronglyMeasurable.const_mul
    apply AEStronglyMeasurable.mul _ hG.aestronglyMeasurable
    exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp ((-(l+d n):ℝ)*((σ:ℂ)+(t:ℂ)*I)))).aestronglyMeasurable
  apply (hG.norm.const_mul (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))).mono' hm
  exact Filter.Eventually.of_forall (fun t => le_of_eq (term_norm G a d σ l n t))

theorem term_integral_norm (G : ℂ → ℂ) (a : ℕ → ℂ) (d : ℕ → ℝ)
    (σ l : ℝ) (n : ℕ) :
    (∫ t : ℝ, ‖term G a d σ l n t‖) =
      (Real.exp (-l*σ)*(‖a n‖*Real.exp (-σ*d n)))*
        (∫ t : ℝ, ‖G ((σ:ℂ)+(t:ℂ)*I)‖) := by
  simp_rw [term_norm]
  exact integral_const_mul _ _

theorem kernel_series (G : ℂ → ℂ) (a : ℕ → ℂ) (d : ℕ → ℝ) (l : ℝ) (z : ℂ) :
    kernel (fun w => G w*series a d w) l z = ∑' n, a n*kernel G (l+d n) z := by
  simp only [kernel, series]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : ((-(l+d n):ℝ):ℂ)*z = ((-l:ℝ):ℂ)*z+((-d n:ℝ):ℂ)*z := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- Generalized sum/integral exchange; the analytic kernel is arbitrary,
but its vertical integrability and the coefficient majorant are explicit. -/
theorem exchange {G : ℂ → ℂ} {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ}
    (hG : VerticalIntegrable G σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n))) (l : ℝ) :
    integral (fun w => G w*series a d w) σ l =
      ∑' n, a n*integral G σ (l+d n) := by
  unfold FinitenessMellinContour.integral
  simp_rw [kernel_series]
  have hsum : Summable (fun n => ∫ t : ℝ, ‖term G a d σ l n t‖) := by
    simp_rw [term_integral_norm]
    exact (ha.mul_left (Real.exp (-l*σ))).mul_right _
  have hh := integral_tsum_of_summable_integral_norm (term_integrable hG a d l) hsum
  change (∫ t : ℝ, ∑' n, term G a d σ l n t) = _
  rw [← hh]
  apply tsum_congr
  intro n
  exact integral_const_mul _ _

theorem inverse {G : ℂ → ℂ} {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ}
    (hG : VerticalIntegrable G σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n))) (l : ℝ) :
    mellinInv σ (fun w => G w*series a d w) (Real.exp l) =
      ∑' n, a n*mellinInv σ G (Real.exp (l+d n)) := by
  rw [mellinInv_eq (Real.exp_pos l), Real.log_exp, exchange hG ha,
    Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [mellinInv_eq (Real.exp_pos (l+d n)), Real.log_exp, Complex.real_smul]
  ring

#print axioms exchange
#print axioms inverse

end MaassMellinSeries
