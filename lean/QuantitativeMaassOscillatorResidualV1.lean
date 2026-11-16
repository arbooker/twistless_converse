module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

open Set MeasureTheory

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The forced oscillator identity in a Banach space. It needs no
eigenbasis or discrete-spectrum hypothesis. -/
theorem oscillator_residual_integral (u v f : ℝ → H) (t : ℝ) (ht : t ≠ 0)
    (hu : ∀ r, HasDerivAt u (v r) r)
    (hv : ∀ r, HasDerivAt v (-(t^2) • u r+f r) r)
    (hf : Continuous f) (hv0 : v 0=0) (s : ℝ) :
    u s-Real.cos (t*s) • u 0 =
      ∫ r in (0:ℝ)..s, (Real.sin (t*(s-r))/t) • f r := by
  let F : ℝ → H := fun r =>
    (Real.sin (t*(s-r))/t) • v r+Real.cos (t*(s-r)) • u r
  have hd (r : ℝ) : HasDerivAt F ((Real.sin (t*(s-r))/t) • f r) r := by
    have hlin : HasDerivAt (fun x : ℝ => t*(s-x)) (-t) r := by
      simpa only [id_eq,mul_neg,mul_one] using
        ((hasDerivAt_id r).const_sub s).const_mul t
    have ha : HasDerivAt (fun x : ℝ => Real.sin (t*(s-x))/t)
        (-Real.cos (t*(s-r))) r := by
      convert hlin.sin.div_const t using 1
      field_simp
    have hc : HasDerivAt (fun x : ℝ => Real.cos (t*(s-x)))
        (t*Real.sin (t*(s-r))) r := by
      convert hlin.cos using 1
      ring
    have hh := (ha.smul (hv r)).add (hc.smul (hu r))
    have hcancel : (Real.sin (t*(s-r))/t)*t^2=t*Real.sin (t*(s-r)) := by
      field_simp
    apply hh.congr_deriv
    calc
      _ = (-(Real.sin (t*(s-r))/t*t^2)+t*Real.sin (t*(s-r))) • u r+
          (Real.sin (t*(s-r))/t) • f r := by module
      _ = _ := by rw [hcancel]; simp
  have hi : IntervalIntegrable (fun r => (Real.sin (t*(s-r))/t) • f r)
      volume 0 s := (by fun_prop : Continuous (fun r => (Real.sin (t*(s-r))/t) • f r)).intervalIntegrable 0 s
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi
  simpa only [F,sub_self,mul_zero,Real.sin_zero,zero_div,zero_smul,Real.cos_zero,
    one_smul,zero_add,hv0,smul_zero,sub_zero] using he.symm

/-- A uniform forcing bound gives the frequency gain `1/t` for
positive frequency, at both positive and negative evolution times. -/
theorem oscillator_residual_norm (u v f : ℝ → H) (t : ℝ) (ht : 0 < t)
    (hu : ∀ r, HasDerivAt u (v r) r)
    (hv : ∀ r, HasDerivAt v (-(t^2) • u r+f r) r)
    (hf : Continuous f) (hv0 : v 0=0) (s C : ℝ)
    (hC : ∀ r ∈ uIoc 0 s, ‖f r‖ ≤ C) :
    ‖u s-Real.cos (t*s) • u 0‖ ≤ |s| * C/t := by
  rw [oscillator_residual_integral u v f t ht.ne' hu hv hf hv0 s]
  have hbound : ∀ r ∈ uIoc 0 s, ‖(Real.sin (t*(s-r))/t) • f r‖ ≤ C/t := by
    intro r hr
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos ht]
    calc
      _ ≤ (1/t)*‖f r‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) ht.le) (norm_nonneg _)
      _ ≤ (1/t)*C := mul_le_mul_of_nonneg_left (hC r hr) (by positivity)
      _ = _ := by ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [sub_zero,mul_div_assoc,mul_comm (C/t)] using hh

#print axioms oscillator_residual_integral
#print axioms oscillator_residual_norm

end QuantitativeMaass
