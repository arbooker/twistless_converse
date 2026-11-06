module

public import GridLevelFormulaV1
public import SpanningActualKernelV1
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace GridRadius

open GridPrimeParts GridAdmissibleGap GridLevelFormula SpanningActualKernel SpanningLevelArithmetic

theorem grid_radius {N G s r : ℕ} (hN : 0<N) (hG : 0<G) (hr : 0<r)
    (hNG : N∣G) (hrG : Nat.Coprime r G) (v : ℕ) :
    let m := primePart G (fun p => p∣s)
    let d := primePart G (fun p => ¬p∣s)
    radius N (G*v) (d*r)=((m:ℝ)*v)/((r:ℝ)*Real.sqrt (levelPart N s)) := by
  let m := primePart G (fun p => p∣s)
  let d := primePart G (fun p => ¬p∣s)
  have hd0 : d≠0 := part_ne_zero (Nat.ne_of_gt hG) _
  have hmd : m*d=G := part_complement (Nat.ne_of_gt hG) _
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd0
  have hrR : (r:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  have hpart : 0<levelPart N s := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hN) _)
  have hroot : Real.sqrt (levelPart N s:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hpart))
  change (G*v:ℕ)/Real.sqrt (Nat.lcm N ((d*r)^2):ℝ)=((m:ℝ)*v)/((r:ℝ)*Real.sqrt (levelPart N s))
  rw [grid_level (Nat.ne_of_gt hN) (Nat.ne_of_gt hG) hNG hrG]
  simp only [Nat.cast_mul,Nat.cast_pow]
  rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (by positivity)]
  have hmdR : (m:ℝ)*d=G := by exact_mod_cast hmd
  rw [←hmdR]
  change ((m:ℝ)*d*v)/(Real.sqrt (levelPart N s)*((d:ℝ)*r))=
    ((m:ℝ)*v)/((r:ℝ)*Real.sqrt (levelPart N s))
  field_simp

theorem order_ratio {N s : ℕ} (hN : Admissible N) (hs : 2<s) :
    (6:ℝ)/5≤(s:ℝ)/Real.sqrt (levelPart N s) := by
  have hn : 0<levelPart N s := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hN.1) _)
  have hp : (0:ℝ)<Real.sqrt (levelPart N s) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hgap : (3:ℝ)*levelPart N s≤2*(s:ℝ)^2 := by exact_mod_cast level_gap hN hs
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (levelPart N s))
  apply (le_div_iff₀ hp).mpr
  have hsR : (0:ℝ)≤s := Nat.cast_nonneg s
  nlinarith

#print axioms grid_radius
#print axioms order_ratio

end GridRadius
