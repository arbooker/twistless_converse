module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 400000
public section

namespace QuantitativeMaass

/-- The squared spectral residual has only cubic growth in the moving
window centre. The remaining factor is a fifth smoothing-kernel moment. -/
theorem window_residual_weight_le (t r u : ℝ) (ht : 1 ≤ t)
    (hu : t ≤ |u|) (hu1 : |u| ≤ t+1) :
    (r^2-t^2)^2 * |r| ≤ 18*t^3*(1+|r-u|)^5 := by
  let x := |r-u|
  have hx : 0 ≤ x := abs_nonneg _
  have ht0 : 0 ≤ t := by linarith
  have hr : |r| ≤ t+1+x := by
    have h := abs_add_le (r-u) u
    rw [sub_add_cancel] at h
    change |r| ≤ x+|u| at h
    linarith
  have hgap : abs (|r|-t) ≤ x+1 := by
    have h := abs_add_le (|r|-|u|) (|u|-t)
    rw [sub_add_sub_cancel] at h
    have hu2 : abs (|u|-t) ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hu)]; linarith
    have hr2 : abs (|r|-|u|) ≤ x := abs_abs_sub_abs_le_abs_sub r u
    linarith
  have hfactor : |r^2-t^2| = abs (|r|-t) * (|r|+t) := by
    rw [← sq_abs r, sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (abs_nonneg r) ht0)]
    ring
  have hres : |r^2-t^2| ≤ 3*t*(1+x)^2 := by
    calc
      _ = abs (|r|-t) * (|r|+t) := hfactor
      _ ≤ (x+1) * (2*t+1+x) :=
        mul_le_mul hgap (by linarith) (add_nonneg (abs_nonneg r) ht0) (by positivity)
      _ ≤ (x+1) * (3*t*(1+x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr ht) hx]
      _ = _ := by ring
  have hr' : |r| ≤ 2*t*(1+x) := by
    apply hr.trans
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hx]
  have hs := pow_le_pow_left₀ (abs_nonneg (r^2-t^2)) hres 2
  rw [sq_abs] at hs
  calc
    _ ≤ (3*t*(1+x)^2)^2 * (2*t*(1+x)) :=
      mul_le_mul hs hr' (abs_nonneg r) (sq_nonneg _)
    _ = _ := by dsimp [x]; ring

#print axioms window_residual_weight_le

end QuantitativeMaass
