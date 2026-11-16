module

public import QuantitativeMaassWeightedSeedGradientV1
public import QuantitativeArithmeticMaassGradientFormV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticClassicalPetersson AsymptoticCongruenceWeight
open scoped Topology

namespace QuantitativeMaass
open QuantitativeArithmeticMaassGradient

def quotientWeightEnergySeed (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) : QuotientEnergySpace N :=
  Classical.choose (quotientWeight_seed_energy_gradient N hε hv w)

theorem quotientWeightEnergySeed_value (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    (energyInclusion N (quotientWeightEnergySeed N hε hv w)).val=
      quotientWeightMultiplier N hε hv (poincareSeedVector N w).val :=
  (Classical.choose_spec (quotientWeight_seed_energy_gradient N hε hv w)).1

theorem quotientWeightEnergySeed_gradient (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) (i : Bool) :
    quotientGradient N i (quotientWeightEnergySeed N hε hv w)=
      quotientWeightMultiplier N hε hv (seedGradientLp N i w)+
        quotientWeightGradientMultiplier N hε hv i (poincareSeedVector N w).val :=
  (Classical.choose_spec (quotientWeight_seed_energy_gradient N hε hv w)).2 i

theorem quotientWeightMultiplier_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : ‖quotientWeightMultiplier N hε hv‖≤quotientWeightBound ε :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (quotientWeightBound_nonneg ε) _

/-- The form bound is uniform over all compact seeds: the support-dependent
constants used to construct the lift disappear from the final estimate. -/
theorem quotientWeightEnergySeed_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    ‖quotientWeightEnergySeed N hε hv w‖≤
      Real.sqrt ((quotientWeightBound ε)^2+
        2*(quotientWeightBound ε+4*quotientWeightBound ε*(2*v:ℝ))^2)*‖poincareEnergySeed N w‖ := by
  let B := quotientWeightBound ε
  let D := 4*quotientWeightBound ε*(2*v:ℝ)
  let U := quotientWeightEnergySeed N hε hv w
  have hB : 0≤B := quotientWeightBound_nonneg ε
  have hD : 0≤D := by dsimp [D]; positivity
  have hM (x : Lp ℂ 2 (quotientMeasure N)) :
      ‖quotientWeightMultiplier N hε hv x‖≤B*‖x‖ :=
    ((quotientWeightMultiplier N hε hv).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (quotientWeightMultiplier_norm N hε hv) (norm_nonneg x))
  have hG (i : Bool) (x : Lp ℂ 2 (quotientMeasure N)) :
      ‖quotientWeightGradientMultiplier N hε hv i x‖≤D*‖x‖ :=
    ((quotientWeightGradientMultiplier N hε hv i).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (quotientWeightGradientMultiplier_norm N hε hv i) (norm_nonneg x))
  have hbase : ‖poincareSeedVector N w‖≤‖poincareEnergySeed N w‖ :=
    energyDomainValue_norm_le N (poincareEnergySeed N w)
  have hmass : ‖energyInclusion N U‖≤B*‖poincareEnergySeed N w‖ := by
    change ‖(energyInclusion N U).val‖≤_
    rw [quotientWeightEnergySeed_value]
    exact (hM _).trans (mul_le_mul_of_nonneg_left hbase hB)
  have hgrad (i : Bool) : ‖quotientGradient N i U‖≤(B+D)*‖poincareEnergySeed N w‖ := by
    rw [quotientWeightEnergySeed_gradient]
    apply (norm_add_le _ _).trans
    apply (add_le_add (hM _) (hG i _)).trans
    calc
      _ ≤ B*‖poincareEnergySeed N w‖+D*‖poincareEnergySeed N w‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (seedGradientLp_norm_le N i w) hB)
          (mul_le_mul_of_nonneg_left hbase hD)
      _ = _ := (add_mul _ _ _).symm
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hmass 2
  have ht2 := pow_le_pow_left₀ (norm_nonneg _) (hgrad true) 2
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) (hgrad false) 2
  have hn := quotientClosedEnergy_norm N U
  rw [quotientGradient_norm_sq] at hn
  have hsq : ‖U‖^2≤(B^2+2*(B+D)^2)*‖poincareEnergySeed N w‖^2 := by
    simp only [mul_pow] at hm2 ht2 hf2
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤B^2+2*(B+D)^2)]
  exact hsq

#print axioms quotientWeightEnergySeed_value
#print axioms quotientWeightEnergySeed_gradient
#print axioms quotientWeightMultiplier_norm
#print axioms quotientWeightEnergySeed_norm

end QuantitativeMaass
