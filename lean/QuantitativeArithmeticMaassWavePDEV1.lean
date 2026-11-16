module

public import QuantitativeArithmeticMaassWaveTheoryV4
public import QuantitativeMaassShiftedWaveDomainV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeArithmeticMaassWave

open QuantitativeMaass QuantitativeMaass.Wave

def quotientWaveVelocity (N : ℕ) (x y : AutomorphicSpace N) (t : ℝ) : AutomorphicSpace N :=
  timePrimitive (fun u => shiftedQuotientWave N u ((1/4 : ℂ) • x-y)) t

/-- Strong first derivative on the whole Friedrichs domain. -/
theorem quotientWave_hasDerivAt (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (t : ℝ) :
    HasDerivAt (fun u => shiftedQuotientWave N u x) (quotientWaveVelocity N x y t) t := by
  have h := range_wave_hasDerivAt (friedrichsResolvent N)
    (friedrichsResolvent_isPositive N) (friedrichsResolvent_opNorm_le N)
    (friedrichsResolvent_denseRange N) (x+y) t
  change friedrichsResolvent N (x+y)=x at hxy
  rw [hxy] at h
  have he : (5/4 : ℝ) • x-(x+y)=(1/4 : ℂ) • x-y := by
    module
  simpa only [he,quotientWaveVelocity,shiftedQuotientWave] using h

theorem quotientWaveVelocity_hasDerivAt (N : ℕ) (x y : AutomorphicSpace N) (t : ℝ) :
    HasDerivAt (quotientWaveVelocity N x y)
      ((1/4 : ℂ) • shiftedQuotientWave N t x-shiftedQuotientWave N t y) t := by
  change HasDerivAt (timePrimitive (fun u => shiftedQuotientWave N u ((1/4 : ℂ) • x-y))) _ t
  have h := timePrimitive_hasDerivAt (shiftedQuotientWave_stronglyContinuous N
    ((1/4 : ℂ) • x-y)) t
  simpa only [map_sub,map_smul] using h

/-- The actual shifted quotient wave solves the strong second-order equation
u''=(1/4)u-Delta u. This is a derivative theorem, not a centered-limit assertion. -/
theorem quotientWave_second_derivative (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (t : ℝ) :
    HasDerivAt (deriv (fun u => shiftedQuotientWave N u x))
      ((1/4 : ℂ) • shiftedQuotientWave N t x-shiftedQuotientWave N t y) t := by
  have he : deriv (fun u => shiftedQuotientWave N u x)=quotientWaveVelocity N x y :=
    funext (fun u => (quotientWave_hasDerivAt N hxy u).deriv)
  rw [he]
  exact quotientWaveVelocity_hasDerivAt N x y t

theorem quotientWave_strong_PDE (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (t : ℝ) :
    FriedrichsGraph N (shiftedQuotientWave N t x) (shiftedQuotientWave N t y) ∧
    HasDerivAt (fun u => shiftedQuotientWave N u x) (quotientWaveVelocity N x y t) t ∧
    HasDerivAt (deriv (fun u => shiftedQuotientWave N u x))
      ((1/4 : ℂ) • shiftedQuotientWave N t x-shiftedQuotientWave N t y) t :=
  ⟨shiftedQuotientWave_graph N t hxy,quotientWave_hasDerivAt N hxy t,
    quotientWave_second_derivative N hxy t⟩

theorem quotientWaveVelocity_zero (N : ℕ) (x y : AutomorphicSpace N) :
    quotientWaveVelocity N x y 0=0 := by
  simp [quotientWaveVelocity,timePrimitive]

#print axioms quotientWave_strong_PDE
#print axioms quotientWaveVelocity_zero

end QuantitativeArithmeticMaassWave
