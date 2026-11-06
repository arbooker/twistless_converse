module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace FinitenessDiskDecay

open Metric Set

/-- Maximum modulus for a holomorphic quotient gives the exact power
decay from a zero of order at least n. No growth hypothesis is used. -/
theorem factor_decay (G H : ℂ → ℂ) (n : ℕ)
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hfactor : ∀ w ∈ ball (0 : ℂ) 1, G w = w^n * H w)
    {R C : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hC : ∀ w : ℂ, ‖w‖ = R → ‖G w‖ ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ R) : ‖G w‖ ≤ (‖w‖/R)^n * C := by
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  have hc := hH.diffContOnCl_ball hsub
  have hp : 0 < R^n := pow_pos hR n
  have hb : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖H z‖ ≤ C / R^n := by
    intro z hz
    have hzR : ‖z‖ = R := by
      simpa only [frontier_ball (0 : ℂ) hR.ne', mem_sphere, dist_zero_right] using hz
    have hzB : z ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right, hzR] using hR1
    have he : ‖G z‖ = R^n * ‖H z‖ := by rw [hfactor z hzB, norm_mul, norm_pow, hzR]
    apply (le_div_iff₀ hp).mpr
    simpa only [mul_comm] using he.symm.trans_le (hC z hzR)
  have hwC : w ∈ closedBall (0 : ℂ) R := by simpa only [mem_closedBall, dist_zero_right] using hw
  have hh : ‖H w‖ ≤ C/R^n :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hc hb
      (by simpa only [closure_ball (0 : ℂ) hR.ne'] using hwC)
  calc
    ‖G w‖ = ‖w‖^n * ‖H w‖ := by rw [hfactor w (hsub hwC), norm_mul, norm_pow]
    _ ≤ ‖w‖^n * (C/R^n) := mul_le_mul_of_nonneg_left hh (pow_nonneg (norm_nonneg _) _)
    _ = (‖w‖/R)^n * C := by rw [div_pow]; ring

noncomputable def quotient (n : ℕ) (G : ℂ → ℂ) : ℂ → ℂ :=
  (fun f : ℂ → ℂ => dslope f 0)^[n] G

theorem quotient_differentiable (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (n : ℕ) : DifferentiableOn ℂ (quotient n G) (ball 0 1) := by
  induction n with
  | zero => exact hG
  | succ n ih =>
      change DifferentiableOn ℂ ((fun f : ℂ → ℂ => dslope f 0)^[n+1] G) (ball 0 1)
      rw [Function.iterate_succ_apply']
      exact (Complex.differentiableOn_dslope (ball_mem_nhds _ (by norm_num))).mpr ih

theorem zero_coeff_factor (G : ℂ → ℂ) (n : ℕ)
    (hzero : ∀ i : ℕ, i < n → quotient i G 0 = 0) (w : ℂ) :
    G w = w^n * quotient n G w := by
  simpa only [sub_zero, smul_eq_mul, quotient, Function.swap] using
    (pow_sub_smul_iterate_dslope_of_zero n hzero w).symm

#print axioms factor_decay
#print axioms quotient_differentiable
#print axioms zero_coeff_factor

end FinitenessDiskDecay
