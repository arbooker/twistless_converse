module

public import FinitenessMellinSeriesV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessDirichletInversion

open Complex MeasureTheory FinitenessFiniteOrder FinitenessBoundaryDecay
  FinitenessMellinContour FinitenessMellinSeries

theorem series_bound {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ}
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n)))
    {z : ℂ} (hz : z.re=σ) :
    ‖series a d z‖ ≤ ∑' n, ‖a n‖*Real.exp (-σ*d n) := by
  have he (n : ℕ) : ‖a n*Complex.exp ((-d n : ℝ)*z)‖ = ‖a n‖*Real.exp (-σ*d n) := by
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hz]
    ring
  have hn : Summable (fun n => ‖a n*Complex.exp ((-d n : ℝ)*z)‖) := by simpa only [he] using ha
  simpa only [series, he] using norm_tsum_le_tsum_norm hn

/-- Absolute convergence of the actual series pays the rapid right-boundary
hypothesis, using the proved Gamma estimates. -/
theorem right_rapid {a : ℕ → ℂ} {d : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n)))
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, z.re=σ → F z=Gamma z*series a d z) : Rapid F σ := by
  have hg : Rapid Gamma σ := by simpa using gamma_shift (α := 0) (by simpa using hσ)
  apply of_norm_le (K := ∑' n, ‖a n‖*Real.exp (-σ*d n)) hg
    (tsum_nonneg (fun n => mul_nonneg (norm_nonneg (a n)) (Real.exp_pos _).le))
  intro z hz
  rw [hF z hz, norm_mul]
  calc
    ‖Gamma z‖*‖series a d z‖ ≤ ‖Gamma z‖*(∑' n, ‖a n‖*Real.exp (-σ*d n)) :=
      mul_le_mul_of_nonneg_left (series_bound ha hz) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem mellinInv_congr_line {F G : ℂ → ℂ} {σ : ℝ}
    (hFG : ∀ z : ℂ, z.re=σ → F z=G z) (x : ℝ) : mellinInv σ F x=mellinInv σ G x := by
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [hFG _ (by simp)]

/-- The analytic inverse-Mellin bridge, now with right-line decay and
sum/integral exchange DISCHARGED from absolute Dirichlet convergence.
Only the specified entire continuation and functional equation are assumed. -/
theorem inversion {a : ℕ → ℂ} {d : ℕ → ℝ} {σ κ : ℝ} (hσ : 0 < σ)
    (hσκ : κ-σ < σ) (ha : Summable (fun n => ‖a n‖*Real.exp (-σ*d n)))
    {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hfinite : Bound F)
    (hF : ∀ z : ℂ, z.re=σ → F z=Gamma z*series a d z)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ z : ℂ, F z=ε*F ((κ : ℂ)-z)) (l : ℝ) :
    (∑' n, a n*(Real.exp (-Real.exp (l+d n)) : ℂ)) =
      ε*Complex.exp ((-l*κ : ℝ):ℂ)*(∑' n, a n*(Real.exp (-Real.exp (-l+d n)) : ℂ)) := by
  have hright := right_rapid hσ ha hF
  have he := FinitenessMellinContour.inversion hhol hfinite hσκ hright hε hFE l
  have hi (t : ℝ) : (1/(2*Real.pi):ℝ) • integral F σ t =
      ∑' n, a n*(Real.exp (-Real.exp (t+d n)) : ℂ) := by
    have hinv := FinitenessMellinSeries.inverse hσ ha t
    rw [← mellinInv_congr_line hF, mellinInv_eq (Real.exp_pos t), Real.log_exp] at hinv
    exact hinv
  rw [← hi l, ← hi (-l), he, Complex.real_smul, Complex.real_smul]
  ring

#print axioms right_rapid
#print axioms inversion

end FinitenessDirichletInversion
