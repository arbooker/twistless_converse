module

public import QuantitativeMaassWindowShellSeparationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace QuantitativeMaass

/-- The actual squared trimmed-window multiplier has a single fourth-power
bound on every integer distance shell outside the original window. -/
theorem shrunken_squaredWindow_floor_tail (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (t ε δ R r : ℝ) (ht : 0<t) (hr : 0≤r) (hε : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1)
    (hR : 0<R) (hout : r∉Icc t (t+ε)) :
    (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) r)^2≤
      (81*(∫ u,|u|^2*K u)^2/(R*δ)^4)/((⌊|r-t|⌋₊:ℝ)+1)^4 := by
  let n := ⌊|r-t|⌋₊
  let m : ℝ := ∫ u,|u|^2*K u
  have hm : 0≤m^2 := sq_nonneg m
  have hRd : 0<R*δ := mul_pos hR hδ
  have hn : 0<(n:ℝ)+1 := by positivity
  have hout' : r∉Icc t (t+ε)∪Icc (-(t+ε)) (-t) := by
    intro h
    rcases h with h|h
    · exact hout h
    · linarith [h.2]
  by_cases hnear : n≤1
  · have hb := shrunken_squaredWindow_tail K hK t ε δ R r hδ hR hout' 2
    norm_num only at hb
    have hnf : (n:ℝ)≤1 := by exact_mod_cast hnear
    have hp : ((n:ℝ)+1)^4≤81 := by
      have hh := pow_le_pow_left₀ hn.le (by linarith : (n:ℝ)+1≤2) 4
      norm_num at hh
      linarith
    calc
      _ ≤ m^2/(R*δ)^4 := hb
      _ ≤ (81*m^2/(R*δ)^4)/((n:ℝ)+1)^4 := by
        apply (le_div_iff₀ (pow_pos hn 4)).mpr
        have hh := mul_le_mul_of_nonneg_left hp (div_nonneg hm (by positivity : 0≤(R*δ)^4))
        convert hh using 1
        ring
  · have hn2 : 2≤n := by omega
    have hn2r : (2:ℝ)≤n := by exact_mod_cast hn2
    have hnm : 0<(n:ℝ)-1 := by linarith
    have hb := shrunken_squaredWindow_shell_tail K hK t ε δ R r n ht.le hr hε hδ.le hR
      (by linarith) (Nat.floor_le (abs_nonneg (r-t))) 2
    norm_num only at hb
    have hp : ((n:ℝ)+1)^4≤81*((n:ℝ)-1)^4 := by
      have hh := pow_le_pow_left₀ hn.le (by linarith : (n:ℝ)+1≤3*((n:ℝ)-1)) 4
      norm_num [mul_pow] at hh
      exact hh
    have hδpow : δ^4≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hδ.le hδ1 4
    have hden : (R*δ)^4*((n:ℝ)+1)^4≤81*(R*((n:ℝ)-1))^4 := by
      calc
        _ = R^4*(δ^4*((n:ℝ)+1)^4) := by rw [mul_pow]; ring
        _ ≤ R^4*(1*(81*((n:ℝ)-1)^4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hδpow hp (by positivity) (by norm_num)) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ m^2/(R*((n:ℝ)-1))^4 := hb
      _ ≤ (81*m^2/(R*δ)^4)/((n:ℝ)+1)^4 := by
        rw [div_div]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_left hden hm
        convert hh using 1
        ring

#print axioms shrunken_squaredWindow_floor_tail

end QuantitativeMaass
