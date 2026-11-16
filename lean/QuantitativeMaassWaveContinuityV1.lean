module

public import QuantitativeMaassWaveCosineV1
public import QuantitativeMaassWaveMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfc_dampedCosine_time_bound (A : H →L[ℂ] H) (t u : ℝ) :
    ‖dampedOperator A t-dampedOperator A u‖≤|t-u| := by
  unfold dampedOperator
  rw [← cfc_sub (a := A) (dampedCosine t) (dampedCosine u) (dampedCosine_continuous t).continuousOn
    (dampedCosine_continuous u).continuousOn]
  exact norm_cfc_le (abs_nonneg _) (fun s _ => dampedCosine_time_bound t u s)

theorem quotientWave_resolvent_time_bound (N : ℕ) (t u : ℝ) (v : AutomorphicSpace N) :
    ‖quotientWave N t (friedrichsResolvent N v)-
      quotientWave N u (friedrichsResolvent N v)‖≤|t-u| *‖v‖ := by
  rw [quotientWave_resolvent,quotientWave_resolvent]
  exact ((dampedOperator (friedrichsResolvent N) t-
    dampedOperator (friedrichsResolvent N) u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (cfc_dampedCosine_time_bound (friedrichsResolvent N) t u) (norm_nonneg v))

theorem quotientWave_dist_le (N : ℕ) (t : ℝ) (v w : AutomorphicSpace N) :
    dist (quotientWave N t v) (quotientWave N t w)≤dist v w := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact quotientWave_apply_norm_le N t (v-w)

/-- Strong continuity on every actual quotient vector, obtained from the
quantitative time estimate on the resolvent range and uniform contraction. -/
theorem quotientWave_stronglyContinuous (N : ℕ) (v : AutomorphicSpace N) :
    Continuous (fun t : ℝ => quotientWave N t v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨w,hw⟩ := (friedrichsResolvent_denseRange N).exists_dist_lt v
    (show 0<ε/4 by positivity)
  let δ : ℝ := ε/(2*(‖w‖+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have hsmall : |u-t| *‖w‖<ε/2 := by
    rw [Real.dist_eq] at hu
    have hden : 0<2*(‖w‖+1) := by positivity
    have hmul := (lt_div_iff₀ hden).mp hu
    nlinarith [abs_nonneg (u-t),norm_nonneg w]
  have hmid := quotientWave_resolvent_time_bound N u t w
  rw [← dist_eq_norm] at hmid
  have htri := dist_triangle (quotientWave N u v)
    (quotientWave N u (friedrichsResolvent N w)) (quotientWave N t v)
  have htri' := dist_triangle (quotientWave N u (friedrichsResolvent N w))
    (quotientWave N t (friedrichsResolvent N w)) (quotientWave N t v)
  have hleft := quotientWave_dist_le N u v (friedrichsResolvent N w)
  have hright := quotientWave_dist_le N t (friedrichsResolvent N w) v
  rw [dist_comm (friedrichsResolvent N w) v] at hright
  linarith

#print axioms quotientWave_resolvent_time_bound
#print axioms quotientWave_stronglyContinuous

end QuantitativeMaass.Wave
