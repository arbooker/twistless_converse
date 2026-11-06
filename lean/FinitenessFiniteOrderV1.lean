module

public import FinitenessExponentialCutoffV1
public import Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

namespace FinitenessFiniteOrder

open Complex Filter Asymptotics Set

/-- A global integer-exponent finite-order envelope. Constants are
individual to the entire function. -/
def Bound (F : ℂ → ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ d : ℕ, ∀ z : ℂ, ‖F z‖ ≤ Real.exp (A*(1+‖z‖)^d)

theorem polynomial_le_exp (d : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x^d ≤ ((Nat.factorial d : ℝ)/c^d)*Real.exp (c*x) := by
  have hh := mul_le_mul_of_nonneg_right
    (FinitenessExponentialCutoff.polynomial_decay_bound d hc hx) (Real.exp_pos (c*x)).le
  have he : Real.exp (-c*x)*Real.exp (c*x) = 1 := by
    rw [← Real.exp_add, show -c*x+c*x=0 by ring, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using hh

/-- Finite order is much smaller than the prior double exponential allowed
by Phragmen-Lindelof, with ANY prescribed positive inner exponent. -/
theorem strip_double_exp {F : ℂ → ℂ} (hF : Bound F) {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c) :
    ∃ B : ℝ, ∀ z : ℂ, |z.re| ≤ R →
      ‖F z‖ ≤ Real.exp (B*Real.exp (c*|z.im|)) := by
  obtain ⟨A,hA,d,hAprod⟩ := hF
  let K := (Nat.factorial d : ℝ)/c^d
  refine ⟨A*(1+R)^d*K*Real.exp c, ?_⟩
  intro z hz
  have hx : 1+‖z‖ ≤ (1+R)*(1+|z.im|) := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    nlinarith [abs_nonneg z.im, mul_nonneg hR (abs_nonneg z.im)]
  have hp := polynomial_le_exp d hc (show 0 ≤ 1+|z.im| by positivity)
  apply (hAprod z).trans
  apply Real.exp_le_exp.mpr
  calc
    A*(1+‖z‖)^d ≤ A*((1+R)*(1+|z.im|))^d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx d) hA
    _ = (A*(1+R)^d)*(1+|z.im|)^d := by rw [mul_pow]; ring
    _ ≤ (A*(1+R)^d)*(K*Real.exp (c*(1+|z.im|))) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hA (pow_nonneg (by positivity) _))
    _ = (A*(1+R)^d*K*Real.exp c)*Real.exp (c*|z.im|) := by
      rw [mul_add, mul_one, Real.exp_add]
      ring

theorem pow_mul {F : ℂ → ℂ} (hF : Bound F) (n : ℕ) :
    Bound (fun z => z^n*F z) := by
  obtain ⟨A,hA,d,hbound⟩ := hF
  refine ⟨A+n, by positivity, d+1, ?_⟩
  intro z
  have hnbase : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have hpn : ‖z‖^n ≤ Real.exp ((n : ℝ)*‖z‖) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hnbase n
  have hd : (1+‖z‖)^d ≤ (1+‖z‖)^(d+1) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)
  have hz : ‖z‖ ≤ (1+‖z‖)^(d+1) := by
    have hh : (1+‖z‖)^1 ≤ (1+‖z‖)^(d+1) :=
      pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by omega)
    rw [pow_one] at hh
    exact (show ‖z‖ ≤ 1+‖z‖ by linarith).trans hh
  calc
    ‖z^n*F z‖ = ‖z‖^n*‖F z‖ := by rw [norm_mul, norm_pow]
    _ ≤ Real.exp ((n : ℝ)*‖z‖)*Real.exp (A*(1+‖z‖)^d) :=
      mul_le_mul hpn (hbound z) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ)*‖z‖+A*(1+‖z‖)^d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+n)*(1+‖z‖)^(d+1)) := Real.exp_le_exp.mpr (by nlinarith)

theorem mul {F G : ℂ → ℂ} (hF : Bound F) (hG : Bound G) :
    Bound (fun z => F z*G z) := by
  obtain ⟨A,hA,d,hf⟩ := hF
  obtain ⟨B,hB,e,hg⟩ := hG
  refine ⟨A+B, add_nonneg hA hB, max d e, ?_⟩
  intro z
  have hd : (1+‖z‖)^d ≤ (1+‖z‖)^(max d e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_max_left _ _)
  have he : (1+‖z‖)^e ≤ (1+‖z‖)^(max d e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_max_right _ _)
  calc
    ‖F z*G z‖ = ‖F z‖*‖G z‖ := norm_mul _ _
    _ ≤ Real.exp (A*(1+‖z‖)^d)*Real.exp (B*(1+‖z‖)^e) :=
      mul_le_mul (hf z) (hg z) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (A*(1+‖z‖)^d+B*(1+‖z‖)^e) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B)*(1+‖z‖)^(max d e)) := Real.exp_le_exp.mpr (by nlinarith)

theorem exp_linear (l : ℝ) : Bound (fun z : ℂ => Complex.exp ((l : ℂ)*z)) := by
  refine ⟨|l|, abs_nonneg _, 1, ?_⟩
  intro z
  rw [Complex.norm_exp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, pow_one]
  apply Real.exp_le_exp.mpr
  calc
    l*z.re ≤ |l*z.re| := le_abs_self _
    _ = |l| * |z.re| := abs_mul _ _
    _ ≤ |l| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)
    _ ≤ |l| * (1+‖z‖) := by nlinarith [abs_nonneg l]

#print axioms mul
#print axioms exp_linear
#print axioms strip_double_exp
#print axioms pow_mul

end FinitenessFiniteOrder
