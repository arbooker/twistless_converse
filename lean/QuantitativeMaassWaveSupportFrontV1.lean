module

public import QuantitativeMaassWaveRegionV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassWeighted QuantitativeArithmeticMaassWave
open QuantitativeArithmeticMaassGradient

theorem shiftedWave_abs_time (N : ℕ) (t : ℝ) :
    Wave.shiftedQuotientWave N |t|=Wave.shiftedQuotientWave N t := by
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    exact Wave.shiftedRangeCosine_neg (friedrichsResolvent N) t

/-- Almost-everywhere vanishing beyond a strict superlevel, at positive or
negative time. The wave is the actual shifted Friedrichs cosine family. -/
theorem wave_superlevel_ae_zero (N : ℕ) (b : Cutoff N)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c d : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (t : ℝ) (hsep : c+|b.gradientBound| * |t|<d) :
    ∀ᵐ Z ∂quotientMeasure N,
      d≤(upperFunction b.value Z).re → (Wave.shiftedQuotientWave N t x).val Z=0 := by
  have hs : MeasurableSet {Z : ℍ | d≤(upperFunction b.value Z).re} :=
    measurableSet_le measurable_const (Complex.continuous_re.comp
      (upperFunction_continuous b.smooth)).measurable
  have h := wave_region_ae_zero N b hxy hyz c d hu hg
    {Z : ℍ | d≤(upperFunction b.value Z).re} hs (fun _ hZ => hZ) (abs_nonneg t) hsep
  rw [shiftedWave_abs_time] at h
  exact h

/-- The actual wave remains in the advancing sublevel set of any bounded
smooth real invariant weight. No support hypothesis is imposed on the wave. -/
theorem wave_weighted_support (N : ℕ) (b : Cutoff N)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (c : ℝ)
    (hu : ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N x y) Z=0)
    (hg : ∀ i : Bool, ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N x y) Z=0)
    (t : ℝ) :
    ∀ᵐ Z ∂quotientMeasure N, c+|b.gradientBound| * |t|<(upperFunction b.value Z).re →
      (Wave.shiftedQuotientWave N t x).val Z=0 := by
  have hq : ∀ q : ℚ, ∀ᵐ Z ∂quotientMeasure N,
      c+|b.gradientBound| * |t|<(q:ℝ) → (q:ℝ)≤(upperFunction b.value Z).re →
        (Wave.shiftedQuotientWave N t x).val Z=0 := by
    intro q
    by_cases hsep : c+|b.gradientBound| * |t|<(q:ℝ)
    · filter_upwards [wave_superlevel_ae_zero N b hxy hyz c q hu hg t hsep] with Z hZ
      exact fun _ => hZ
    · exact Eventually.of_forall (fun _ h => False.elim (hsep h))
  filter_upwards [ae_all_iff.mpr hq] with Z hZ
  intro hout
  obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hout
  exact hZ q hq₁ hq₂.le

#print axioms wave_superlevel_ae_zero
#print axioms wave_weighted_support

end QuantitativeMaass.Weighted
