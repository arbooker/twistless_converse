module

public import FinitenessFiniteOrderV1
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open Complex MeasureTheory Set

/-- A quadratic exponential envelope for every real power multiplied
 by a fixed decaying exponential. -/
theorem rpow_exp_bound {c r t : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (ht : 0 < t) :
    t ^ r * Real.exp (-c * t) ≤
      Real.exp (2 * r ^ 2 / c) * Real.exp (-(c / 2) * t) := by
  have hl : Real.log t ≤ 2 * Real.sqrt t := by
    have hh := Real.log_le_rpow_div ht.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hs := sq_nonneg (c * Real.sqrt t - 2 * r)
  have ht' : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have he : Real.log t * r - c * t ≤ 2 * r ^ 2 / c - c / 2 * t := by
    have hh := mul_le_mul_of_nonneg_right hl hr
    have hsq : c * (2 * Real.sqrt t * r - c / 2 * t) ≤ 2 * r ^ 2 := by
      nlinarith [congrArg (fun x : ℝ => c ^ 2 * x) ht']
    rw [mul_comm] at hsq
    have hd := (le_div_iff₀ hc).mpr hsq
    linarith
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [he]

/-- The part of the Mellin transform above height one. -/
def upperMellin (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) * f t

theorem upperMellin_norm_le (f : ℝ → ℂ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-c * t)) (s : ℂ) :
    ‖upperMellin f s‖ ≤ C * (2 / c) * Real.exp (2 * (1 + ‖s‖) ^ 2 / c) := by
  let B := C * Real.exp (2 * (1 + ‖s‖) ^ 2 / c)
  have hB : 0 ≤ B := mul_nonneg hC (Real.exp_pos _).le
  have hi : IntegrableOn (fun t : ℝ => B * Real.exp (-(c / 2) * t)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(c / 2) < 0) 1).const_mul B
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1),
      ‖(t : ℂ) ^ (s - 1) * f t‖ ≤ B * Real.exp (-(c / 2) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hp : ‖(t : ℂ) ^ (s - 1)‖ ≤ t ^ (1 + ‖s‖) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply Real.rpow_le_rpow_of_exponent_le ht.le
      simp only [Complex.sub_re, Complex.one_re]
      linarith [Complex.re_le_norm s]
    calc
      ‖(t : ℂ) ^ (s - 1) * f t‖ ≤ t ^ (1 + ‖s‖) * (C * Real.exp (-c * t)) := by
        rw [norm_mul]
        exact mul_le_mul hp (hf t ht.le) (norm_nonneg _) (Real.rpow_pos_of_pos ht0 _).le
      _ = C * (t ^ (1 + ‖s‖) * Real.exp (-c * t)) := by ring
      _ ≤ C * (Real.exp (2 * (1 + ‖s‖) ^ 2 / c) * Real.exp (-(c / 2) * t)) :=
        mul_le_mul_of_nonneg_left (rpow_exp_bound hc (by positivity) ht0) hC
      _ = B * Real.exp (-(c / 2) * t) := by dsimp [B]; ring
  have hh := norm_integral_le_of_norm_le hi hb
  change ‖upperMellin f s‖ ≤ _ at hh
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(c / 2) < 0), mul_one] at hh
  have he : -Real.exp (-(c / 2)) / -(c / 2) ≤ 2 / c := by
    have hx : Real.exp (-(c / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    field_simp
    nlinarith
  calc
    ‖upperMellin f s‖ ≤ B * (-Real.exp (-(c / 2)) / -(c / 2)) := hh
    _ ≤ B * (2 / c) := mul_le_mul_of_nonneg_left he hB
    _ = _ := by dsimp [B]; ring

/-- Exponential decay gives a finite-order envelope for the upper Mellin
 integral, with no growth hypothesis on its complex argument. -/
theorem upperMellin_finiteOrder (f : ℝ → ℂ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-c * t)) :
    FinitenessFiniteOrder.Bound (upperMellin f) := by
  let D := C * (2 / c)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + 2 / c, by positivity, 2, ?_⟩
  intro s
  have hd : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hr : 1 ≤ (1 + ‖s‖) ^ 2 := by nlinarith [norm_nonneg s]
  calc
    ‖upperMellin f s‖ ≤ D * Real.exp (2 * (1 + ‖s‖) ^ 2 / c) :=
      upperMellin_norm_le f hC hc hf s
    _ ≤ Real.exp D * Real.exp (2 * (1 + ‖s‖) ^ 2 / c) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
    _ = Real.exp (D + 2 * (1 + ‖s‖) ^ 2 / c) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((D + 2 / c) * (1 + ‖s‖) ^ 2) := by
      apply Real.exp_le_exp.mpr
      calc
        D + 2 * (1 + ‖s‖) ^ 2 / c ≤ D * (1 + ‖s‖) ^ 2 + 2 * (1 + ‖s‖) ^ 2 / c := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left hr hD]
        _ = _ := by ring

#print axioms rpow_exp_bound
#print axioms upperMellin_norm_le
#print axioms upperMellin_finiteOrder

end AsymptoticClassicalLSeries
