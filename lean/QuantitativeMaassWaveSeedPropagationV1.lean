module

public import QuantitativeMaassWaveSupportFrontV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassWave QuantitativeArithmeticMaassGradient

/-- Invariance of the separating weight preserves seed support under the
literal Poincare sum. -/
theorem poincare_sublevel_support (N : ℕ) (b : Cutoff N) (u : SmoothUpperSeed) (c : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0) :
    tsupport (upperFunction (congruencePoincareCartesian N u.toFun))⊆
      {Z : ℍ | (upperFunction b.value Z).re≤c} := by
  apply closure_minimal
  · intro Z hZ
    by_contra hn
    have hc : c<(upperFunction b.value Z).re := lt_of_not_ge hn
    apply hZ
    rw [congruencePoincareCartesian_represents]
    change (∑' g : gamma N, upperFunction u.toFun (g•Z))=0
    calc
      _ = ∑' _ : gamma N, (0:ℂ) := by
        apply tsum_congr
        intro g
        exact hu (g•Z) (by rw [b.invariant]; exact hc)
      _ = 0 := tsum_zero
  · exact isClosed_le (Complex.continuous_re.comp (upperFunction_continuous b.smooth))
      continuous_const

theorem graphEnergyLift_seed (N : ℕ) (u : SmoothUpperSeed) :
    graphEnergyLift N (poincareSeedVector N u) (poincareSeedVector N u.laplacian)=
      (poincareEnergySeed N u : QuotientEnergySpace N) := by
  apply energyInclusion_injective N
  rw [graphEnergyLift_value N (friedrichsGraph_poincareSeed N u),
    energyInclusion_coe,poincareEnergySeed_value]

theorem seed_initial_value_support (N : ℕ) (b : Cutoff N) (u : SmoothUpperSeed) (c : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0) :
    ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      ambientInclusion N (graphEnergyLift N (poincareSeedVector N u)
        (poincareSeedVector N u.laplacian)) Z=0 := by
  have hi : ambientInclusion N (graphEnergyLift N (poincareSeedVector N u)
      (poincareSeedVector N u.laplacian))=(poincareSeedVector N u).val :=
    congrArg Subtype.val (graphEnergyLift_value N (friedrichsGraph_poincareSeed N u))
  rw [hi]
  filter_upwards [poincareSeedVector_coeFn N u] with Z hZ
  intro hc
  rw [hZ,← congruencePoincareCartesian_represents]
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  exact (not_le.mpr hc) (poincare_sublevel_support N b u c hu hm)

/-- For smooth Poincare data the gradient-support requirement is a theorem,
not an additional condition on initial data. -/
theorem seed_initial_gradient_support (N : ℕ) (b : Cutoff N) (u : SmoothUpperSeed) (c : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0)
    (i : Bool) :
    ∀ᵐ Z ∂quotientMeasure N, c<(upperFunction b.value Z).re →
      quotientGradient N i (graphEnergyLift N (poincareSeedVector N u)
        (poincareSeedVector N u.laplacian)) Z=0 := by
  rw [graphEnergyLift_seed,quotientGradient_seed]
  filter_upwards [(seedGradient_memLp N i u).coeFn_toLp] with Z hZ
  intro hc
  rw [show seedGradientLp N i u Z=seedGradient N i u Z from hZ]
  have hn : Z∉tsupport (upperFunction (congruencePoincareCartesian N u.toFun)) := by
    intro hm
    exact (not_le.mpr hc) (poincare_sublevel_support N b u c hu hm)
  change (Z.im:ℂ)*MaassDifferential.dir (axis i) (congruencePoincareCartesian N u.toFun)
    (Z.re,Z.im)=0
  rw [upper_dir_zero_of_notMem_tsupport hn,mul_zero]

/-- Weighted finite propagation for every actual smooth compact Poincare seed.
Both operator-domain conditions and initial gradient support are discharged
from the seed construction. -/
theorem poincare_wave_weighted_support (N : ℕ) (b : Cutoff N) (u : SmoothUpperSeed) (c : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0)
    (t : ℝ) :
    ∀ᵐ Z ∂quotientMeasure N, c+|b.gradientBound| * |t|<(upperFunction b.value Z).re →
      (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val Z=0 :=
  wave_weighted_support N b (friedrichsGraph_poincareSeed N u)
    (friedrichsGraph_poincareSeed N u.laplacian) c
    (seed_initial_value_support N b u c hu) (seed_initial_gradient_support N b u c hu) t

#print axioms seed_initial_gradient_support
#print axioms poincare_wave_weighted_support

end QuantitativeMaass.Weighted
