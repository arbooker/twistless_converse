module

public import QuantitativeMaassWeightedSeedEnergyValueV1
public import QuantitativeMaassPoincareGradientLimitV1
public import QuantitativeMaassWeightedSeedProductRuleV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential QuantitativeArithmeticMaassGradient

/-- The literal weighted seed has an actual quotient energy lift with the exact
bounded-multiplier product rule for both completed gradient columns. -/
theorem quotientWeight_seed_energy_gradient (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    ∃ U : QuotientEnergySpace N,
      (energyInclusion N U).val=quotientWeightMultiplier N hε hv (poincareSeedVector N w).val ∧
      ∀ i : Bool,quotientGradient N i U=
        quotientWeightMultiplier N hε hv (seedGradientLp N i w)+
          quotientWeightGradientMultiplier N hε hv i (poincareSeedVector N w).val := by
  obtain ⟨u,U,hvalue,hU,ha,K,hK,hs⟩ := quotientWeight_seed_energy_realization N hε hv w
  let f : Point → ℂ := fun W => (quotientWeightPlane N ε v W:ℂ)*
    upperSeedExtension (upperFunction w.toFun) W
  obtain ⟨L,hf⟩ := quotientWeight_seed_lipschitz N hε hv w
  have hfu : upperFunction f=(fun z => (weight N ε v z:ℂ)*upperFunction w.toFun z) := by
    funext z
    change (quotientWeightPlane N ε v (z.re,z.im):ℂ)*
      upperSeedExtension (upperFunction w.toFun) (z.re,z.im)=_
    rw [quotientWeightPlane_upper,upperSeedExtension_positive w.toFun _ z.im_pos]
    rfl
  have hfc : HasCompactSupport (upperFunction f) := by
    rw [hfu]
    exact w.compact.mono (Function.support_mul_subset_right _ _)
  refine ⟨U,hvalue,?_⟩
  intro i
  have hrep := quotientGradient_limit_representative N i (K∪tsupport (upperFunction f))
    (hK.union hfc) u hf (fun n => (hs n).trans subset_union_left) subset_union_right ha hU
  apply Lp.ext
  filter_upwards [hrep,quotientWeight_seed_gradient_product_ae N hε hv i w,
    (seedGradient_memLp N i w).coeFn_toLp,poincareSeedVector_coeFn N w,
    AsymptoticL2Multiplier.operator_coeFn (fun z => (weight N ε v z:ℂ))
      (Complex.measurable_ofReal.comp (weight_measurable N ε v)).aestronglyMeasurable
      (Eventually.of_forall (quotientWeight_complex_bound N hε hv)) (seedGradientLp N i w),
    AsymptoticL2Multiplier.operator_coeFn (quotientWeightGradientColumn N ε v i)
      (quotientWeightGradientColumn_measurable N ε v i).aestronglyMeasurable
      (Eventually.of_forall (quotientWeightGradientColumn_bound N hε hv i)) (poincareSeedVector N w).val,
    Lp.coeFn_add (quotientWeightMultiplier N hε hv (seedGradientLp N i w))
      (quotientWeightGradientMultiplier N hε hv i (poincareSeedVector N w).val)]
    with z hz hp hg hw hm hd hadd
  change quotientWeightMultiplier N hε hv (seedGradientLp N i w) z=
    (weight N ε v z:ℂ)*seedGradientLp N i w z at hm
  change quotientWeightGradientMultiplier N hε hv i (poincareSeedVector N w).val z=
    quotientWeightGradientColumn N ε v i z*(poincareSeedVector N w).val z at hd
  change seedGradientLp N i w z=seedGradient N i w z at hg
  rw [hadd,Pi.add_apply,hm,hd,hg,hw,hz]
  exact hp

#print axioms quotientWeight_seed_energy_gradient

end QuantitativeMaass
