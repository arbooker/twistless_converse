module

public import MaassMellinSeriesV1
public import MaassGammaRapidV1
public import FinitenessDirichletInversionV1

set_option autoImplicit false

@[expose] public section

open Complex MeasureTheory FinitenessBoundaryDecay FinitenessMellinContour
  FinitenessMellinSeries FinitenessFiniteOrder

namespace MaassMellin

theorem rapid_translate {G : ℂ → ℂ} {c δ : ℝ} (hG : Rapid G (c+δ)) :
    Rapid (fun z => G (z+(δ:ℂ))) c := by
  intro n
  obtain ⟨C0,h0⟩ := hG 0
  obtain ⟨Cn,hn⟩ := hG n
  refine ⟨2^(n-1)*(Cn+|δ|^n*C0), ?_⟩
  intro z hz
  have hw : (z+(δ:ℂ)).re=c+δ := by simp only [add_re, ofReal_re, hz]
  have hzero : ‖G (z+(δ:ℂ))‖≤C0 := by simpa only [pow_zero, one_mul] using h0 _ hw
  have hp := hn _ hw
  have hb : ‖z‖≤‖z+(δ:ℂ)‖+|δ| := by
    calc
      ‖z‖ = ‖(z+(δ:ℂ))-(δ:ℂ)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z+(δ:ℂ)‖+‖(δ:ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hpow : ‖z‖^n≤2^(n-1)*(‖z+(δ:ℂ)‖^n+|δ|^n) :=
    (pow_le_pow_left₀ (norm_nonneg _) hb n).trans
      (add_pow_le (norm_nonneg _) (abs_nonneg _) n)
  calc
    ‖z‖^n*‖G (z+(δ:ℂ))‖ ≤
        (2^(n-1)*(‖z+(δ:ℂ)‖^n+|δ|^n))*‖G (z+(δ:ℂ))‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2^(n-1)*(‖z+(δ:ℂ)‖^n*‖G (z+(δ:ℂ))‖+|δ|^n*‖G (z+(δ:ℂ))‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hp (mul_le_mul_of_nonneg_left hzero (by positivity))) (by positivity)

theorem parityGamma_rapid (p : MaassSpectral.Parameter) (δ : ℕ) {c : ℝ} (hc : 1<c) :
    Rapid (fun s => realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))) c := by
  have hb : |(MaassSpectral.order p).re|<c+(δ:ℝ) := by
    have h := order_re_bound p
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  simpa only [ofReal_natCast] using rapid_translate (realGammaPair_rapid hb)

theorem parityGamma_vertical (p : MaassSpectral.Parameter) (δ : ℕ) {c : ℝ} (hc : 1<c) :
    VerticalIntegrable (fun s => realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))) c := by
  have hb : |(MaassSpectral.order p).re|<c+(δ:ℝ) := by
    have h := order_re_bound p
    linarith [Nat.cast_nonneg (α := ℝ) δ]
  apply (realGammaPair_vertical hb).congr
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  congr 1
  push_cast
  ring

theorem completed_right_rapid {G F : ℂ → ℂ} {a : ℕ → ℂ} {d : ℕ → ℝ} {c : ℝ}
    (hG : Rapid G c) (ha : Summable (fun n => ‖a n‖*Real.exp (-c*d n)))
    (hF : ∀ z : ℂ, z.re=c → F z=G z*series a d z) : Rapid F c := by
  apply of_norm_le hG (tsum_nonneg (fun n =>
    mul_nonneg (norm_nonneg (a n)) (Real.exp_pos _).le))
  intro z hz
  rw [hF z hz, norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (FinitenessDirichletInversion.series_bound ha hz) (norm_nonneg (G z))

theorem parity_series_inverse (p : MaassSpectral.Parameter) (δ : ℕ)
    {a : ℕ → ℂ} {d : ℕ → ℝ} {c : ℝ} (hc : 1<c)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-c*d n))) (l : ℝ) :
    mellinInv c (fun s => realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))*series a d s)
      (Real.exp l) = ∑' n, a n*parityKernel p δ (Real.exp (l+d n)) := by
  rw [MaassMellinSeries.inverse (parityGamma_vertical p δ hc) ha]
  apply tsum_congr
  intro n
  rw [parity_inverse_mellin p δ hc (Real.exp_pos _)]

/-- Axis inversion from an entire finite-order completed Dirichlet series.
Only absolute convergence on a right line remains as a coefficient input;
kernel inversion, rapid decay and the sum/integral exchange are proved. -/
theorem parity_axis_inversion (p : MaassSpectral.Parameter) (δ : ℕ)
    {a : ℕ → ℂ} {d : ℕ → ℝ} {c : ℝ} (hc : 1<c)
    (ha : Summable (fun n => ‖a n‖*Real.exp (-c*d n)))
    {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hfinite : Bound F)
    (hF : ∀ z : ℂ, z.re=c →
      F z=realGammaPair (MaassSpectral.order p) (z+(δ:ℂ))*series a d z)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ z : ℂ, F z=ε*F (1-z)) (l : ℝ) :
    (∑' n, a n*parityKernel p δ (Real.exp (l+d n))) =
      ε*(Real.exp (-l):ℂ)*(∑' n, a n*parityKernel p δ (Real.exp (-l+d n))) := by
  have hr := completed_right_rapid (parityGamma_rapid p δ hc) ha hF
  have he := FinitenessMellinContour.inversion hhol hfinite
    (κ := 1) (by linarith : 1-c<c) hr hε (by simpa only [ofReal_one] using hFE) l
  have hi (t:ℝ) : (1/(2*Real.pi):ℝ) • integral F c t =
      ∑' n, a n*parityKernel p δ (Real.exp (t+d n)) := by
    have hinv := parity_series_inverse p δ hc ha t
    rw [← FinitenessDirichletInversion.mellinInv_congr_line hF,
      mellinInv_eq (Real.exp_pos t), Real.log_exp] at hinv
    exact hinv
  rw [← hi l, ← hi (-l), he, Complex.real_smul, Complex.real_smul]
  simp only [mul_one, ofReal_neg, ofReal_exp]
  ring

#print axioms parity_series_inverse
#print axioms parity_axis_inversion

end MaassMellin
