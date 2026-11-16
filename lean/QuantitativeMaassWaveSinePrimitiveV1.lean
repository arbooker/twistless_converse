module

public import QuantitativeArithmeticMaassWaveEnergyRegularityV1
public import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

open QuantitativeArithmeticMaassWave

/-- The strong time primitive of the actual shifted cosine family. -/
def quotientSine (N : ℕ) (t : ℝ) (v : AutomorphicSpace N) : AutomorphicSpace N :=
  timePrimitive (fun u => shiftedQuotientWave N u v) t

theorem quotientSine_hasDerivAt (N : ℕ) (v : AutomorphicSpace N) (t : ℝ) :
    HasDerivAt (fun u => quotientSine N u v) (shiftedQuotientWave N t v) t :=
  timePrimitive_hasDerivAt (shiftedQuotientWave_stronglyContinuous N v) t

theorem quotientSine_zero (N : ℕ) (v : AutomorphicSpace N) : quotientSine N 0 v=0 := by
  simp [quotientSine,timePrimitive]

theorem quotientSine_graph (N : ℕ) {v w : AutomorphicSpace N}
    (hvw : FriedrichsGraph N v w) (t : ℝ) :
    FriedrichsGraph N (quotientSine N t v) (quotientSine N t w) :=
  friedrichsGraph_timePrimitive N _ _ (shiftedQuotientWave_stronglyContinuous N v)
    (shiftedQuotientWave_stronglyContinuous N w)
    (fun u => shiftedQuotientWave_graph N u hvw) t

theorem quotientWaveVelocity_eq_sine (N : ℕ) (v w : AutomorphicSpace N) (t : ℝ) :
    quotientWaveVelocity N v w t=(1/4 : ℂ) • quotientSine N t v-quotientSine N t w := by
  unfold quotientWaveVelocity quotientSine timePrimitive
  simp only [map_sub,map_smul]
  have hf : IntervalIntegrable (fun u => (1/4 : ℂ) • shiftedQuotientWave N u v) volume 0 t :=
    ((shiftedQuotientWave_stronglyContinuous N v).const_smul (1/4 : ℂ)).intervalIntegrable 0 t
  have hg : IntervalIntegrable (fun u => shiftedQuotientWave N u w) volume 0 t :=
    (shiftedQuotientWave_stronglyContinuous N w).intervalIntegrable 0 t
  rw [intervalIntegral.integral_sub hf hg,intervalIntegral.integral_smul]


#print axioms quotientSine_graph
#print axioms quotientWaveVelocity_eq_sine

end QuantitativeMaass.Wave
