module

public import GridRadiusV1

@[expose] public section

namespace GridBufferedWindow

open SpanningWindows

theorem window_from_excess {rad centre v r R : ℝ} {t u : ℤ}
    (hr : 0<r) (hR : 0<R) (hrR : r≤R) (hv : 16*R≤v)
    (hcentre : v/r≤centre) (hrad : centre+v/(5*r)≤rad)
    (ht : |(t:ℝ)|≤v/(8*R)) (hu : (u:ℝ)=centre+(t:ℝ)) :
    Legal rad u ∧ 3*v/(40*R)-1≤rad-1-(u:ℝ) := by
  have hv0 : 0<v := by nlinarith
  have hR0 : R≠0 := ne_of_gt hR
  have ht1 : (t:ℝ)≤v/(8*R) := (le_abs_self _).trans ht
  have ht2 : -(v/(8*R))≤(t:ℝ) := by have := neg_le_abs (t:ℝ); linarith
  have hsmall : v/(5*R)≤v/(5*r) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hvr : v/R≤v/r := by
    apply (div_le_div_iff₀ hR hr).mpr
    exact mul_le_mul_of_nonneg_left hrR hv0.le
  have hidentity : v/(5*R)-v/(8*R)=3*v/(40*R) := by field_simp; ring
  have hmargin : 3*v/(40*R)-1≤rad-1-(u:ℝ) := by rw [hu]; linarith
  have hpositive : 0<3*v/(40*R)-1 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<40*R)).mpr
    nlinarith
  have hzero : 0<v/R-v/(8*R) := by
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<8*R) hR).mpr
    nlinarith
  have hu0 : 0<(u:ℝ) := by rw [hu]; linarith
  refine ⟨⟨?_,?_⟩,hmargin⟩ <;> linarith

theorem excess_from_ratio {m c s v r n : ℝ}
    (hc : 1≤c) (hv : 0≤v) (hr : 0<r)
    (hmc : m=c*s) (hratio : (6:ℝ)/5≤s/n) :
    c*v/r+v/(5*r)≤m*v/(r*n) := by
  have hc0 : 0≤c := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hratio hc0
  have hcoef : c+1/5≤c*(s/n) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (div_nonneg hv hr.le)
  have hleft : (c+1/5)*(v/r)=c*v/r+v/(5*r) := by ring
  have hright : c*(s/n)*(v/r)=m*v/(r*n) := by rw [hmc]; ring
  rwa [hleft,hright] at hmul

#print axioms window_from_excess
#print axioms excess_from_ratio

end GridBufferedWindow
