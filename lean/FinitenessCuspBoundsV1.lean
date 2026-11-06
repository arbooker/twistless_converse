module

public import FinitenessDiskDecayV1
public import FinitenessExponentialCutoffV1
public import Mathlib.Analysis.Complex.Periodic

@[expose] public section

namespace FinitenessCuspBounds

open Metric Set FinitenessDiskDecay
open Function.Periodic

/-- Holomorphy at the cusp and a zero constant term supply all the positive
height bounds needed by the envelope argument. -/
theorem tail (F G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (h0 : G 0 = 0) (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    (b : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ z : ℂ, η ≤ z.im → z.im^b * ‖F z‖ ≤ M := by
  let R := Real.exp (-2 * Real.pi * η)
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  have hH := quotient_differentiable G hG 1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hH.continuousOn.mono hsub)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simpa using hR.le))
  have hfactor (w : ℂ) : G w = w * quotient 1 G w := by
    simpa only [pow_one] using zero_coeff_factor G 1
      (fun i hi => by
        have hi0 : i = 0 := by omega
        subst i
        exact h0) w
  refine ⟨C * ((Nat.factorial b : ℝ) / (2*Real.pi)^b), ?_⟩
  intro z hz
  have hz0 := hη.trans_le hz
  have hq : ‖qParam 1 z‖ ≤ R := by
    rw [norm_qParam, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hbound : ‖F z‖ ≤ Real.exp (-2*Real.pi*z.im) * C := by
    rw [heq z hz0, hfactor, norm_mul, norm_qParam, div_one]
    exact mul_le_mul_of_nonneg_left (hC _ (by simpa using hq)) (Real.exp_pos _).le
  calc
    z.im^b * ‖F z‖ ≤ z.im^b * (Real.exp (-2*Real.pi*z.im)*C) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hz0.le _)
    _ = C * (z.im^b * Real.exp (-(2*Real.pi)*z.im)) := by ring_nf
    _ ≤ C * ((Nat.factorial b : ℝ) / (2*Real.pi)^b) :=
      mul_le_mul_of_nonneg_left
        (FinitenessExponentialCutoff.polynomial_decay_bound b (by positivity) hz0.le) hC0

/-- Every point on the q-circle is the image of a point on a fixed horizontal
line. Thus the global weighted bound controls the whole circle. -/
theorem circle_bound (F G : ℂ → ℂ)
    (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    (b : ℕ) {M η : ℝ} (hη : 0 < η)
    (hM : ∀ z : ℂ, 0 < z.im → z.im^b * ‖F z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ = Real.exp (-2*Real.pi*η)) :
    ‖G w‖ ≤ M / η^b := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (hw ▸ (Real.exp_pos _).ne')
  let z := invQParam 1 w
  have him : z.im = η := by
    dsimp [z]
    rw [im_invQParam, hw, Real.log_exp]
    field_simp
  have hz : 0 < z.im := him ▸ hη
  have he : F z = G w := by rw [heq z hz, qParam_right_inv (by norm_num) hw0]
  apply (le_div_iff₀ (pow_pos hη b)).mpr
  simpa only [him, he, mul_comm] using hM z hz

/-- Vanishing of the first n Taylor coefficients gives exponential decay
away from any positive horizontal line. -/
theorem height_decay (F G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    (b n : ℕ) (hzero : ∀ i < n, quotient i G 0 = 0)
    {M η : ℝ} (hη : 0 < η)
    (hM : ∀ z : ℂ, 0 < z.im → z.im^b * ‖F z‖ ≤ M)
    {z : ℂ} (hz : η ≤ z.im) :
    ‖F z‖ ≤ Real.exp (-2*Real.pi*(z.im-η)*(n : ℝ)) * (M/η^b) := by
  have hR1 : Real.exp (-2*Real.pi*η) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hq : ‖qParam 1 z‖ ≤ Real.exp (-2*Real.pi*η) := by
    rw [norm_qParam, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hd := factor_decay G (quotient n G) n (quotient_differentiable G hG n)
    (fun w _ => zero_coeff_factor G n hzero w) (Real.exp_pos _) hR1
    (fun w hw => circle_bound F G heq b hη hM hw) hq
  rw [heq z (hη.trans_le hz)]
  convert hd using 1
  rw [norm_qParam, div_one, ← Real.exp_sub, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The linear Taylor cutoff contracts the entire weighted tail by e^-1. -/
theorem weighted_decay (F G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (heq : ∀ z : ℂ, 0 < z.im → F z = G (qParam 1 z))
    (b n : ℕ) (hzero : ∀ i < n, quotient i G 0 = 0)
    {M η : ℝ} (hη : 0 < η) (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, 0 < z.im → z.im^b * ‖F z‖ ≤ M)
    (hn : (b : ℝ)+1 ≤ 2*Real.pi*(n : ℝ)*η)
    {z : ℂ} (hz : 2*η ≤ z.im) :
    z.im^b * ‖F z‖ ≤ Real.exp (-1) * M := by
  have hy : η ≤ z.im := by linarith
  have hz0 : 0 < z.im := hη.trans_le hy
  have ht : 2 ≤ z.im/η := (le_div_iff₀ hη).mpr hz
  have he : -2*Real.pi*(z.im-η)*(n : ℝ) =
      -(2*Real.pi*(n : ℝ)*η)*(z.im/η-1) := by field_simp
  have hd := height_decay F G hG heq b n hzero hη hM hy
  calc
    z.im^b * ‖F z‖
        ≤ z.im^b * (Real.exp (-2*Real.pi*(z.im-η)*(n : ℝ)) * (M/η^b)) :=
      mul_le_mul_of_nonneg_left hd (pow_nonneg hz0.le _)
    _ = ((z.im/η)^b * Real.exp (-(2*Real.pi*(n : ℝ)*η)*(z.im/η-1))) * M := by
      rw [he, div_pow]
      ring
    _ ≤ Real.exp (-1)*M := mul_le_mul_of_nonneg_right
      (FinitenessExponentialCutoff.contraction b ht hn) hM0

#print axioms tail
#print axioms circle_bound
#print axioms height_decay
#print axioms weighted_decay

end FinitenessCuspBounds
