module

public import QuantitativeMaassWeightedSeedEnergyBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open scoped Topology

namespace QuantitativeMaass
open QuantitativeArithmeticMaassGradient

/-- The actual weighted energy lift is linear, by its already identified value
and injectivity of the completed energy inclusion. -/
def quotientWeightSmoothEnergyMap (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : smoothSeedModule →ₗ[ℂ] QuotientEnergySpace N where
  toFun u := quotientWeightEnergySeed N hε hv (moduleSeed u)
  map_add' u w := by
    apply energyInclusion_injective N
    apply Subtype.ext
    rw [map_add]
    change (energyInclusion N (quotientWeightEnergySeed N hε hv (moduleSeed (u+w)))).val=
      (energyInclusion N (quotientWeightEnergySeed N hε hv (moduleSeed u))).val+
        (energyInclusion N (quotientWeightEnergySeed N hε hv (moduleSeed w))).val
    rw [quotientWeightEnergySeed_value,quotientWeightEnergySeed_value,quotientWeightEnergySeed_value]
    have he : poincareSeedVector N (moduleSeed (u+w))=
        poincareSeedVector N (moduleSeed u)+poincareSeedVector N (moduleSeed w) :=
      poincareSeedVector_add N (moduleSeed u) (moduleSeed w)
    rw [he]
    exact map_add (quotientWeightMultiplier N hε hv) _ _
  map_smul' c u := by
    apply energyInclusion_injective N
    apply Subtype.ext
    rw [map_smul]
    change (energyInclusion N (quotientWeightEnergySeed N hε hv (moduleSeed (c•u)))).val=
      c•(energyInclusion N (quotientWeightEnergySeed N hε hv (moduleSeed u))).val
    rw [quotientWeightEnergySeed_value,quotientWeightEnergySeed_value]
    have he : poincareSeedVector N (moduleSeed (c•u))=c•poincareSeedVector N (moduleSeed u) :=
      poincareSeedVector_smul N c (moduleSeed u)
    rw [he]
    exact map_smul (quotientWeightMultiplier N hε hv) c _

theorem quotientWeightSmoothEnergyMap_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (u : smoothSeedModule) :
    ‖quotientWeightSmoothEnergyMap N hε hv u‖≤
      Real.sqrt ((quotientWeightBound ε)^2+
        2*(quotientWeightBound ε+4*quotientWeightBound ε*(2*v:ℝ))^2)*‖smoothEnergyMap N u‖ := by
  change ‖quotientWeightEnergySeed N hε hv (moduleSeed u)‖≤
    _*‖(poincareEnergySeed N (moduleSeed u) : QuotientEnergySpace N)‖
  rw [Completion.norm_coe]
  exact quotientWeightEnergySeed_norm N hε hv (moduleSeed u)

/-- Multiplication by the literal nonsmooth orbit weight extends to a bounded
operator on the actual quotient energy completion. -/
def quotientWeightEnergyMultiplier (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : QuotientEnergySpace N →L[ℂ] QuotientEnergySpace N :=
  (quotientWeightSmoothEnergyMap N hε hv).extendOfNorm (smoothEnergyMap N)

theorem quotientWeightEnergyMultiplier_seed (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    quotientWeightEnergyMultiplier N hε hv (poincareEnergySeed N w)=
      quotientWeightEnergySeed N hε hv w :=
  LinearMap.extendOfNorm_eq (f := quotientWeightSmoothEnergyMap N hε hv)
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N)
    ⟨_,quotientWeightSmoothEnergyMap_bound N hε hv⟩ (seedModule w)

theorem quotientWeightEnergyMultiplier_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    ‖quotientWeightEnergyMultiplier N hε hv‖≤Real.sqrt ((quotientWeightBound ε)^2+
      2*(quotientWeightBound ε+4*quotientWeightBound ε*(2*v:ℝ))^2) :=
  LinearMap.opNorm_extendOfNorm_le (f := quotientWeightSmoothEnergyMap N hε hv)
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N) (Real.sqrt_nonneg _)
    (quotientWeightSmoothEnergyMap_bound N hε hv)

#print axioms quotientWeightSmoothEnergyMap_bound
#print axioms quotientWeightEnergyMultiplier_seed
#print axioms quotientWeightEnergyMultiplier_norm

end QuantitativeMaass
