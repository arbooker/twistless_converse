module

public import GridSelectedWindowsV1

@[expose] public section

namespace GridSpecialWindows

open SpanningActualKernel SpanningLevelArithmetic SpanningWindows

theorem radius_ge_scale {N G q v : ℕ} (hN : 0<N) (hG : 0<G) (hq : 0<q)
    (hNG : N∣G) (hqG : q∣G) : (v:ℝ)≤radius N (G*v) q := by
  have hlev : level N q∣G^2 := Nat.lcm_dvd
    (hNG.trans (by exact ⟨G,by ring⟩)) (pow_dvd_pow_of_dvd hqG 2)
  have hle : level N q≤G^2 := Nat.le_of_dvd (pow_pos hG _) hlev
  have hroot : Real.sqrt (level N q:ℝ)≤G := Real.sqrt_le_iff.mpr
    ⟨Nat.cast_nonneg _,by exact_mod_cast hle⟩
  have hpos : (0:ℝ)<Real.sqrt (level N q) :=
    Real.sqrt_pos.mpr (by exact_mod_cast level_pos hN hq)
  unfold radius
  apply (le_div_iff₀ hpos).mpr
  simp only [Nat.cast_mul]
  nlinarith [show (0:ℝ)≤v from Nat.cast_nonneg v]

theorem special_buffer {rad v R : ℝ} {t : ℤ} (hR : 1≤R) (hv : 16*R≤v)
    (hrad : v≤rad) (ht : |(t:ℝ)|≤v/(8*R)) :
    Legal rad t ∧ 3*v/(40*R)-1≤rad-1-(t:ℝ) := by
  have hRpos : 0<R := by linarith
  have hvpos : 0<v := by nlinarith
  have hsmall : v/(8*R)≤v/8 := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<8*R) (by norm_num : (0:ℝ)<8)).mpr
    nlinarith
  have hmargin : 3*v/(40*R)≤3*v/40 := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<40*R) (by norm_num : (0:ℝ)<40)).mpr
    nlinarith
  have hupper := (le_abs_self (t:ℝ)).trans ht
  have hlower := neg_le_abs (t:ℝ)
  refine ⟨⟨?_,?_⟩,?_⟩ <;> linarith

theorem special_window {N G q v R : ℕ} (hN : 0<N) (hG : 0<G) (hq : 0<q)
    (hNG : N∣G) (hqG : q∣G) (hR : 1≤R) (hv : 16*R≤v)
    (t : ℤ) (ht : |(t:ℝ)|≤(v:ℝ)/(8*R)) :
    Legal (radius N (G*v) q) t ∧
      3*(v:ℝ)/(40*R)-1≤radius N (G*v) q-1-(t:ℝ) :=
  special_buffer (by exact_mod_cast hR) (by exact_mod_cast hv)
    (radius_ge_scale hN hG hq hNG hqG) ht

#print axioms special_window

end GridSpecialWindows
