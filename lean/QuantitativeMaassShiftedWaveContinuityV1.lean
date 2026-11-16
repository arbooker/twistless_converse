module

public import QuantitativeMaassShiftedWaveRangeV1
public import QuantitativeMaassShiftedWaveJointScalarV1
public import Mathlib.Topology.CompactOpen

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shiftedDampedOperator_continuous (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    Continuous (shiftedDampedOperator A) := by
  have hp : Continuous (fun p : ℝ × spectrum ℝ A => (p.1, (p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  let F : C(ℝ × spectrum ℝ A, ℝ) := ⟨fun p => shiftedDampedCosine p.1 p.2,
    shiftedDampedCosine_jointlyContinuous.comp hp⟩
  have hc := (cfcHom_continuous hA).comp F.curry.continuous
  have he : shiftedDampedOperator A = fun t => cfcHom hA (F.curry t) := by
    funext t
    exact cfc_apply (shiftedDampedCosine t) A hA (shiftedDampedCosine_continuous t).continuousOn
  rw [he]
  exact hc

theorem shiftedRangeCosine_dist_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) (v w : H) :
    dist (shiftedRangeCosine A t v) (shiftedRangeCosine A t w) ≤
      Real.cosh (|t|/2) * dist v w := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact ((shiftedRangeCosine A t).le_opNorm (v-w)).trans
    (mul_le_mul_of_nonneg_right (shiftedRangeCosine_norm_le A hA hd t) (norm_nonneg _))

/-- The dense-range extension is strongly continuous, even though its
exceptional-spectrum operator norm need not be at most one. -/
theorem shiftedRangeCosine_stronglyContinuous (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (v : H) : Continuous (fun t => shiftedRangeCosine A t v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let C := Real.cosh ((|t|+1)/2)
  have hC : 0 < C := Real.cosh_pos _
  obtain ⟨w, hw⟩ := hd.exists_dist_lt v (show 0 < ε/(4*C) by positivity)
  have hc : Continuous (fun u => shiftedDampedOperator A u w) :=
    (ContinuousLinearMap.apply ℂ H w).continuous.comp (shiftedDampedOperator_continuous A hA)
  obtain ⟨δ, hδ, hmid⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := t))
    (ε/2) (by positivity)
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro u hu
  have hu1 : |u-t| < 1 := by
    exact (Real.dist_eq u t ▸ hu).trans_le (min_le_left _ _)
  have huδ : dist u t < δ := hu.trans_le (min_le_right _ _)
  have huC : Real.cosh (|u|/2) ≤ C := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ |u|/2),
      abs_of_nonneg (by positivity : 0 ≤ (|t|+1)/2)]
    have hab : |u| ≤ |u-t|+|t| := by
      simpa using abs_add_le (u-t) t
    linarith
  have htC : Real.cosh (|t|/2) ≤ C := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ |t|/2),
      abs_of_nonneg (by positivity : 0 ≤ (|t|+1)/2)]
    linarith
  have hleft := (shiftedRangeCosine_dist_le A hA hd u v (A w)).trans
    (mul_le_mul_of_nonneg_right huC (dist_nonneg : 0 ≤ dist v (A w)))
  have hright := (shiftedRangeCosine_dist_le A hA hd t (A w) v).trans
    (mul_le_mul_of_nonneg_right htC (dist_nonneg : 0 ≤ dist (A w) v))
  rw [dist_comm (A w) v] at hright
  have hm := hmid huδ
  change dist (cfc (shiftedDampedCosine u) A w) (cfc (shiftedDampedCosine t) A w) < ε/2 at hm
  rw [← shiftedRangeCosine_range A hA hd, ← shiftedRangeCosine_range A hA hd] at hm
  have hs : C * dist v (A w) < ε/4 := by
    have hh := (lt_div_iff₀ (show 0 < 4*C by positivity)).mp hw
    nlinarith
  have htri := dist_triangle (shiftedRangeCosine A u v)
    (shiftedRangeCosine A u (A w)) (shiftedRangeCosine A t v)
  have htri' := dist_triangle (shiftedRangeCosine A u (A w))
    (shiftedRangeCosine A t (A w)) (shiftedRangeCosine A t v)
  linarith

theorem shiftedQuotientWave_stronglyContinuous (N : ℕ) (v : AutomorphicSpace N) :
    Continuous (fun t => shiftedQuotientWave N t v) :=
  shiftedRangeCosine_stronglyContinuous _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) v

#print axioms shiftedDampedOperator_continuous
#print axioms shiftedQuotientWave_stronglyContinuous

end QuantitativeMaass.Wave
