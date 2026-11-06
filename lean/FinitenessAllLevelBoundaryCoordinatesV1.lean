module

public import FinitenessAllLevelBoundaryGeometryV1
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelBoundaryCoordinates

open Complex Metric Set MeasureTheory FinitenessAllLevelBoundaryGeometry

/-- The periodic real coordinate of a point on a q-circle. -/
def coordinate (w : ℂ) : ℝ := Int.fract (Function.Periodic.invQParam 1 w).re

theorem coordinate_measurable : Measurable coordinate :=
  (Complex.continuous_re.measurable.comp
    (measurable_const.mul Complex.measurable_log)).fract

theorem coordinate_nonneg (w : ℂ) : 0 ≤ coordinate w := Int.fract_nonneg _

theorem coordinate_lt_one (w : ℂ) : coordinate w < 1 := Int.fract_lt_one _

def selector (Q : ℕ) (hQ : 0 < Q) (w : ℂ) : Fin Q :=
  ⟨Nat.floor ((Q : ℝ) * coordinate w) % Q, Nat.mod_lt _ hQ⟩

theorem selector_measurable (Q : ℕ) (hQ : 0 < Q) : Measurable (selector Q hQ) :=
  (measurable_of_countable (fun n : ℕ => (⟨n % Q, Nat.mod_lt n hQ⟩ : Fin Q))).comp
    ((measurable_const.mul coordinate_measurable).nat_floor)

theorem selector_bounds (Q : ℕ) (hQ : 0 < Q) (w : ℂ) :
    ((selector Q hQ w).val : ℝ) / Q ≤ coordinate w ∧
      coordinate w ≤ (((selector Q hQ w).val : ℝ) + 1) / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hprod : 0 ≤ (Q : ℝ) * coordinate w := mul_nonneg hQ'.le (coordinate_nonneg w)
  have hlt : Nat.floor ((Q : ℝ) * coordinate w) < Q :=
    (Nat.floor_lt hprod).mpr (by nlinarith [coordinate_lt_one w])
  simp only [selector, Nat.mod_eq_of_lt hlt]
  constructor
  · exact (div_le_iff₀ hQ').mpr (by simpa only [mul_comm] using Nat.floor_le hprod)
  · exact (le_div_iff₀ hQ').mpr (by simpa only [mul_comm] using
      (Nat.lt_floor_add_one ((Q : ℝ) * coordinate w)).le)

def radius (b : ℝ) : ℝ := Real.exp (-2 * Real.pi * b)

theorem radius_pos (b : ℝ) : 0 < radius b := Real.exp_pos _

theorem radius_lt_one {b : ℝ} (hb : 0 < b) : radius b < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hp := Real.pi_pos
  nlinarith

/-- The chosen periodic line coordinate maps back to the original q-circle
point, including points where the principal argument jumps. -/
theorem qParam_coordinate {b : ℝ} {w : ℂ} (hw : w ∈ sphere (0 : ℂ) (radius b)) :
    Function.Periodic.qParam 1 (line (coordinate w) b) = w := by
  have hwn : ‖w‖ = radius b := by simpa only [mem_sphere, dist_zero_right] using hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hwn ▸ radius_pos b)
  have him : (Function.Periodic.invQParam 1 w).im = b := by
    rw [Function.Periodic.im_invQParam, hwn, radius, Real.log_exp]
    field_simp
  have he : line (coordinate w) b = Function.Periodic.invQParam 1 w -
      (Int.floor (Function.Periodic.invQParam 1 w).re : ℂ) := by
    apply Complex.ext
    · simp only [line, coordinate, add_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, sub_re, Complex.intCast_re]
      rfl
    · simpa only [line_im, sub_im, Complex.intCast_im, sub_zero] using him.symm
  rw [he]
  have hp : Function.Periodic (Function.Periodic.qParam 1) (1 : ℂ) :=
    FinitenessFourierConstruction.q_periodic
  have hperiod := (hp.zsmul (Int.floor (Function.Periodic.invQParam 1 w).re)).sub_eq
    (Function.Periodic.invQParam 1 w)
  simpa only [zsmul_eq_mul, mul_one, Function.Periodic.qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hw0]
    using hperiod

#print axioms coordinate_measurable
#print axioms selector_measurable
#print axioms selector_bounds
#print axioms qParam_coordinate

end FinitenessAllLevelBoundaryCoordinates
