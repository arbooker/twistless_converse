module

public import QuantitativeArithmeticMaassWavePDEV1
public import QuantitativeMaassFriedrichsFormV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeArithmeticMaassWave

open QuantitativeMaass QuantitativeMaass.Wave

/-- The canonical form-domain representative of an operator-domain vector. -/
def graphEnergyLift (N : ℕ) (x y : AutomorphicSpace N) : QuotientEnergySpace N :=
  (energyInclusion N).adjoint (x+y)

theorem graphEnergyLift_value (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) : energyInclusion N (graphEnergyLift N x y)=x := hxy

theorem graphEnergyLift_form (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (v : QuotientEnergySpace N) :
    quotientClosedEnergy N v (graphEnergyLift N x y)=inner ℂ (energyInclusion N v) y := by
  change inner ℂ v ((energyInclusion N).adjoint (x+y))-
    inner ℂ (energyInclusion N v) (friedrichsResolvent N (x+y))=_
  rw [(energyInclusion N).adjoint_inner_right,hxy,inner_add_right]
  ring

theorem friedrichsGraph_timePrimitive (N : ℕ) (f g : ℝ → AutomorphicSpace N)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ u, FriedrichsGraph N (f u) (g u)) (t : ℝ) :
    FriedrichsGraph N (timePrimitive f t) (timePrimitive g t) := by
  have hsum : timePrimitive f t+timePrimitive g t=timePrimitive (fun u => f u+g u) t :=
    (intervalIntegral.integral_add (hf.intervalIntegrable 0 t) (hg.intervalIntegrable 0 t)).symm
  change friedrichsResolvent N (timePrimitive f t+timePrimitive g t)=timePrimitive f t
  rw [hsum]
  have he := map_timePrimitive ((friedrichsResolvent N).restrictScalars ℝ)
    (fun u => f u+g u) (hf.add hg) t
  change friedrichsResolvent N (timePrimitive (fun u => f u+g u) t)=_ at he
  rw [he]
  congr 1
  exact funext hfg

theorem friedrichsGraph_shifted_pair (N : ℕ) {x y z : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z) :
    FriedrichsGraph N ((1/4 : ℂ) • x-y) ((1/4 : ℂ) • y-z) := by
  change friedrichsResolvent N (((1/4 : ℂ) • x-y)+((1/4 : ℂ) • y-z))=_
  have he : ((1/4 : ℂ) • x-y)+((1/4 : ℂ) • y-z)=
      (1/4 : ℂ) • (x+y)-(y+z) := by module
  rw [he,map_sub,map_smul,hxy,hyz]

theorem quotientWaveVelocity_graph (N : ℕ) {x y z : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z) (t : ℝ) :
    FriedrichsGraph N (quotientWaveVelocity N x y t) (quotientWaveVelocity N y z t) :=
  friedrichsGraph_timePrimitive N _ _ (shiftedQuotientWave_stronglyContinuous N _)
    (shiftedQuotientWave_stronglyContinuous N _)
    (fun u => shiftedQuotientWave_graph N u (friedrichsGraph_shifted_pair N hxy hyz)) t

/-- The actual wave lifted to the completed Dirichlet-form domain. -/
def quotientEnergyWave (N : ℕ) (x y : AutomorphicSpace N) (t : ℝ) : QuotientEnergySpace N :=
  graphEnergyLift N (shiftedQuotientWave N t x) (shiftedQuotientWave N t y)

theorem quotientEnergyWave_value (N : ℕ) {x y : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (t : ℝ) :
    energyInclusion N (quotientEnergyWave N x y t)=shiftedQuotientWave N t x :=
  graphEnergyLift_value N (shiftedQuotientWave_graph N t hxy)

theorem quotientEnergyWave_continuous (N : ℕ) (x y : AutomorphicSpace N) :
    Continuous (quotientEnergyWave N x y) :=
  (energyInclusion N).adjoint.continuous.comp
    ((shiftedQuotientWave_stronglyContinuous N x).add (shiftedQuotientWave_stronglyContinuous N y))

/-- The time derivative exists in the energy norm when the initial vector
lies in the second operator domain. In particular this applies to every
smooth compact Poincare seed. -/
theorem quotientEnergyWave_hasDerivAt (N : ℕ) {x y z : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z) (t : ℝ) :
    HasDerivAt (quotientEnergyWave N x y)
      (graphEnergyLift N (quotientWaveVelocity N x y t) (quotientWaveVelocity N y z t)) t := by
  have h := ((energyInclusion N).adjoint.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((quotientWave_hasDerivAt N hxy t).add (quotientWave_hasDerivAt N hyz t))
  exact h

theorem quotientEnergyWave_derivative_value (N : ℕ) {x y z : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z) (t : ℝ) :
    energyInclusion N (deriv (quotientEnergyWave N x y) t)=quotientWaveVelocity N x y t := by
  rw [(quotientEnergyWave_hasDerivAt N hxy hyz t).deriv]
  exact graphEnergyLift_value N (quotientWaveVelocity_graph N hxy hyz t)

#print axioms quotientEnergyWave_hasDerivAt
#print axioms quotientEnergyWave_derivative_value

end QuantitativeArithmeticMaassWave
