module

public import AsymptoticUnweightedFourierKernelV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane

noncomputable def hyperbolicKernelTerm (h n : ℕ) (ε : ℝ) (z u : ℍ) : ℂ :=
  (z.im*u.im : ℝ) * kernelTerm h n ε z u

theorem hyperbolicKernelTerm_norm (h n : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    ‖hyperbolicKernelTerm h n ε z u‖ =
      (4*Real.pi)^(2*h+1) * (z.im*u.im)^(h+1) / ((2*h).factorial : ℝ) *
        (n+1 : ℕ)^(2*h+1) * (Real.exp (-2*Real.pi*(z.im+u.im)))^(n+1) := by
  have he : (2*Real.pi*Complex.I*(difference z u : ℂ)).re = -2*Real.pi*(z.im+u.im) := by
    simp [difference, Complex.mul_re, Complex.mul_im]
  rw [hyperbolicKernelTerm, kernelTerm_formula h n hε z u]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_exp, he,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos z.im_pos, abs_of_pos u.im_pos, pow_succ]
  norm_num
  ring

noncomputable def termMajorant (h : ℕ) (Y H : ℝ) (n : ℕ) : ℝ :=
  (4*Real.pi)^(2*h+1) * H^(2*h+2) / ((2*h).factorial : ℝ) *
    (n+1 : ℕ)^(2*h+1) * (Real.exp (-4*Real.pi*Y))^(n+1)

theorem hyperbolicKernelTerm_bound (h n : ℕ) {ε Y H : ℝ} (hε : 0 < ε) (_hY : 0 < Y)
    (z u : ℍ) (hYz : Y ≤ z.im) (hYu : Y ≤ u.im) (hHz : z.im ≤ H) (hHu : u.im ≤ H) :
    ‖hyperbolicKernelTerm h n ε z u‖ ≤ termMajorant h Y H n := by
  have hH : 0 < H := z.im_pos.trans_le hHz
  have hp : (z.im*u.im)^(h+1) ≤ H^(2*h+2) := by
    have hh := pow_le_pow_left₀ (mul_nonneg z.im_pos.le u.im_pos.le)
      (mul_le_mul hHz hHu u.im_pos.le hH.le) (h+1)
    simpa only [← pow_two, ← pow_mul, show 2*(h+1)=2*h+2 by omega] using hh
  have he : (Real.exp (-2*Real.pi*(z.im+u.im)))^(n+1) ≤
      (Real.exp (-4*Real.pi*Y))^(n+1) := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  rw [hyperbolicKernelTerm_norm h n hε z u]
  unfold termMajorant
  apply mul_le_mul _ he (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem termMajorant_summable (h : ℕ) {Y : ℝ} (hY : 0 < Y) (H : ℝ) :
    Summable (termMajorant h Y H) := by
  have hr : ‖Real.exp (-4*Real.pi*Y)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hs0 : Summable (fun n : ℕ => (n : ℝ)^(2*h+1) * (Real.exp (-4*Real.pi*Y))^n) :=
    summable_pow_mul_geometric_of_norm_lt_one (2*h+1) hr
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(2*h+1) * (Real.exp (-4*Real.pi*Y))^(n+1)) :=
    (summable_nat_add_iff 1).mpr hs0
  have hh := hs.mul_left ((4*Real.pi)^(2*h+1) * H^(2*h+2) / ((2*h).factorial : ℝ))
  apply hh.congr
  intro n
  unfold termMajorant
  ring

#print axioms hyperbolicKernelTerm_norm
#print axioms hyperbolicKernelTerm_bound
#print axioms termMajorant_summable

end AsymptoticUnweightedKernel
