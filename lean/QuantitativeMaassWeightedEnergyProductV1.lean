module

public import QuantitativeMaassWeightedEnergyExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceWeight
open scoped Topology

namespace QuantitativeMaass
open QuantitativeArithmeticMaassGradient

/-- The completed energy multiplier remains the literal orbit-weight multiplier
under the injective inclusion into actual quotient L². -/
theorem quotientWeightEnergyMultiplier_value (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (U : QuotientEnergySpace N) :
    (energyInclusion N (quotientWeightEnergyMultiplier N hε hv U)).val=
      quotientWeightMultiplier N hε hv (energyInclusion N U).val := by
  have he : (fun U : QuotientEnergySpace N =>
      (energyInclusion N (quotientWeightEnergyMultiplier N hε hv U)).val)=
      (fun U => quotientWeightMultiplier N hε hv (energyInclusion N U).val) := by
    apply (smoothEnergyMap_dense N).equalizer (by fun_prop) (by fun_prop)
    funext u
    change (energyInclusion N (quotientWeightEnergyMultiplier N hε hv
      (poincareEnergySeed N (moduleSeed u)))).val=
        quotientWeightMultiplier N hε hv (energyInclusion N (poincareEnergySeed N (moduleSeed u))).val
    rw [quotientWeightEnergyMultiplier_seed,energyInclusion_coe,poincareEnergySeed_value,
      quotientWeightEnergySeed_value]
  exact congrFun he U

/-- Exact product rule for the actual nonsmooth orbit weight on the entire
constructed energy domain. It follows from the checked seed rule by density. -/
theorem quotientWeightEnergyMultiplier_gradient (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (i : Bool) (U : QuotientEnergySpace N) :
    quotientGradient N i (quotientWeightEnergyMultiplier N hε hv U)=
      quotientWeightMultiplier N hε hv (quotientGradient N i U)+
        quotientWeightGradientMultiplier N hε hv i (energyInclusion N U).val := by
  have he : (fun U : QuotientEnergySpace N =>
      quotientGradient N i (quotientWeightEnergyMultiplier N hε hv U))=
      (fun U => quotientWeightMultiplier N hε hv (quotientGradient N i U)+
        quotientWeightGradientMultiplier N hε hv i (energyInclusion N U).val) := by
    apply (smoothEnergyMap_dense N).equalizer (by fun_prop) (by fun_prop)
    funext u
    change quotientGradient N i (quotientWeightEnergyMultiplier N hε hv
      (poincareEnergySeed N (moduleSeed u)))=
        quotientWeightMultiplier N hε hv (quotientGradient N i (poincareEnergySeed N (moduleSeed u)))+
        quotientWeightGradientMultiplier N hε hv i (energyInclusion N (poincareEnergySeed N (moduleSeed u))).val
    rw [quotientWeightEnergyMultiplier_seed,quotientGradient_seed,energyInclusion_coe,
      poincareEnergySeed_value,quotientWeightEnergySeed_gradient]
  exact congrFun he U

theorem quotientWeightEnergyMultiplier_mass_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (U : QuotientEnergySpace N) :
    ‖energyInclusion N (quotientWeightEnergyMultiplier N hε hv U)‖≤
      quotientWeightBound ε*‖energyInclusion N U‖ := by
  change ‖(energyInclusion N (quotientWeightEnergyMultiplier N hε hv U)).val‖≤
    quotientWeightBound ε*‖(energyInclusion N U).val‖
  rw [quotientWeightEnergyMultiplier_value]
  exact ((quotientWeightMultiplier N hε hv).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (quotientWeightMultiplier_norm N hε hv) (norm_nonneg _))

theorem quotientWeightMultiplier_adjoint (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    (quotientWeightMultiplier N hε hv).adjoint=quotientWeightMultiplier N hε hv :=
  AsymptoticL2Multiplier.operator_adjoint _ _ _ (Eventually.of_forall (fun _ => by simp))

#print axioms quotientWeightEnergyMultiplier_value
#print axioms quotientWeightEnergyMultiplier_gradient
#print axioms quotientWeightEnergyMultiplier_mass_bound
#print axioms quotientWeightMultiplier_adjoint

end QuantitativeMaass
