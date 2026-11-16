module

public import QuantitativeMaassWeightedEnergyProductV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology

namespace QuantitativeMaass

/-- The literal orbit-weight action on the full automorphic Hilbert space,
obtained from its proved mass bound on the dense energy inclusion. -/
def quotientWeightAutomorphicMultiplier (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  ((energyInclusion N).comp (quotientWeightEnergyMultiplier N hε hv)).toLinearMap.extendOfNorm
    (energyInclusion N).toLinearMap

theorem quotientWeightAutomorphicMultiplier_form (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (U : QuotientEnergySpace N) :
    quotientWeightAutomorphicMultiplier N hε hv (energyInclusion N U)=
      energyInclusion N (quotientWeightEnergyMultiplier N hε hv U) :=
  LinearMap.extendOfNorm_eq
    (f := ((energyInclusion N).comp (quotientWeightEnergyMultiplier N hε hv)).toLinearMap)
    (e := (energyInclusion N).toLinearMap) (energyInclusion_denseRange N)
    ⟨quotientWeightBound ε,quotientWeightEnergyMultiplier_mass_bound N hε hv⟩ U

theorem quotientWeightAutomorphicMultiplier_value (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (u : AutomorphicSpace N) :
    (quotientWeightAutomorphicMultiplier N hε hv u).val=
      quotientWeightMultiplier N hε hv u.val := by
  have he : (fun u : AutomorphicSpace N => (quotientWeightAutomorphicMultiplier N hε hv u).val)=
      (fun u => quotientWeightMultiplier N hε hv u.val) := by
    apply (energyInclusion_denseRange N).equalizer (by fun_prop) (by fun_prop)
    funext U
    change (quotientWeightAutomorphicMultiplier N hε hv (energyInclusion N U)).val=
      quotientWeightMultiplier N hε hv (energyInclusion N U).val
    rw [quotientWeightAutomorphicMultiplier_form,quotientWeightEnergyMultiplier_value]
  exact congrFun he u

theorem quotientWeightAutomorphicMultiplier_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    ‖quotientWeightAutomorphicMultiplier N hε hv‖≤quotientWeightBound ε :=
  LinearMap.opNorm_extendOfNorm_le
    (f := ((energyInclusion N).comp (quotientWeightEnergyMultiplier N hε hv)).toLinearMap)
    (e := (energyInclusion N).toLinearMap) (energyInclusion_denseRange N)
    (quotientWeightBound_nonneg ε) (quotientWeightEnergyMultiplier_mass_bound N hε hv)

#print axioms quotientWeightAutomorphicMultiplier_form
#print axioms quotientWeightAutomorphicMultiplier_value
#print axioms quotientWeightAutomorphicMultiplier_norm

end QuantitativeMaass
