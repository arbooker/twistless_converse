module

public import QuantitativeMaassPoincareSobolevCauchyV1
public import QuantitativeMaassCoordinateMassLimitV1
public import QuantitativeMaassCompactPoincareLimitV1
public import QuantitativeMaassQuotientWeightGramV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The energy-space limit represents multiplication by the literal orbit
weight. The value is identified by strong L² convergence of the same seeds. -/
theorem quotientWeight_seed_energy_realization (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    ∃ (u : ℕ → SmoothUpperSeed) (U : QuotientEnergySpace N),
      (energyInclusion N U).val=quotientWeightMultiplier N hε hv (poincareSeedVector N w).val ∧
      Tendsto (fun n => smoothEnergyMap N (seedModule (u n))) atTop (𝓝 U) ∧
      (∀ᵐ Z ∂(volume : Measure Point),
        Tendsto (fun n => fderiv ℝ (u n).toFun Z) atTop
          (𝓝 (fderiv ℝ (fun W => (quotientWeightPlane N ε v W:ℂ)*
            upperSeedExtension (upperFunction w.toFun) W) Z))) ∧
      ∃ K : Set ℍ,IsCompact K ∧ ∀ n,tsupport (upperFunction (u n).toFun)⊆K := by
  let f : Point → ℂ := fun Z => (quotientWeightPlane N ε v Z:ℂ)*
    upperSeedExtension (upperFunction w.toFun) Z
  obtain ⟨L,K,u,hK,hs,hu,hm,hd,ha⟩ := quotientWeight_seed_sobolev_approx N hε hv w
  obtain ⟨Lf,hf⟩ := quotientWeight_seed_lipschitz N hε hv w
  have hc : HasCompactSupport f := (upperSeedExtension_compact _ w.compact).mono
    (Function.support_mul_subset_right _ _)
  have hp : tsupport f⊆{Z : Point | 0<Z.2} :=
    tsupport_mul_subset_right.trans (upperSeedExtension_support_positive _ w.compact)
  have hC := smooth_energy_approximation_cauchy N K hK hf hc u hs hu hm hd
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete hC
  have hfU : upperFunction f=(fun z => (weight N ε v z:ℂ)*upperFunction w.toFun z) := by
    funext z
    change (quotientWeightPlane N ε v (z.re,z.im):ℂ)*
      upperSeedExtension (upperFunction w.toFun) (z.re,z.im)=_
    rw [quotientWeightPlane_upper,upperSeedExtension_positive w.toFun _ z.im_pos]
    rfl
  have hfc : HasCompactSupport (upperFunction f) := by
    rw [hfU]
    exact w.compact.mono (Function.support_mul_subset_right _ _)
  have hft : Continuous (upperFunction f) := hf.continuous.comp (continuous_re.prodMk continuous_im)
  let K' := K∪tsupport (upperFunction f)
  have hK' : IsCompact K' := hK.union hfc
  have hus : ∀ n,tsupport (upperFunction (u n).toFun)⊆K' :=
    fun n => (hs n).trans subset_union_left
  have hfs : tsupport (upperFunction f)⊆K' := subset_union_right
  have hmU := compact_upper_mass_tendsto K' hK' (fun n => (u n).toFun) f
    (fun n => (hu n).1.continuous) hf.continuous
    (fun n => (hu n).2.1) hc (fun n => (hu n).2.2.1) hp hus hfs hm
  have hfL : MemLp (upperFunction f) 2 volume := hft.memLp_of_hasCompactSupport hfc
  have huL (n : ℕ) : MemLp (upperFunction (u n).toFun) 2 volume :=
    (upperFunction_continuous (u n).smooth).memLp_of_hasCompactSupport (u n).compact
  have hmp := compact_poincare_square_tendsto volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K' hK'
    (fun n => upperFunction (u n).toFun) (upperFunction f)
    (fun n => (upperFunction_continuous (u n).smooth).measurable) hft.measurable
    (fun n => (subset_tsupport _).trans (hus n)) ((subset_tsupport _).trans hfs) huL hfL hmU
  let hfP := compact_poincare_memLp volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K' hK'
    (upperFunction f) hft.measurable ((subset_tsupport _).trans hfs) hfL
  have ht := tendsto_toLp_of_square_energy
    (fun n => poincareSum (G := gamma N) (upperFunction (u n).toFun))
    (fun n => (poincareSeed_representative N (u n)).2.2)
    (poincareSum (G := gamma N) (upperFunction f)) hfP hmp
  have htv : Tendsto (fun n => (poincareSeedVector N (u n)).val) atTop
      (𝓝 ((energyInclusion N U).val)) := by
    have hh := ((AutomorphicSpace N).subtypeL.continuous.comp (energyInclusion N).continuous).tendsto U |>.comp hU
    change Tendsto (fun n => (energyInclusion N (smoothEnergyMap N (seedModule (u n)))).val)
      atTop (𝓝 ((energyInclusion N U).val)) at hh
    simpa only [smoothEnergyMap_seed,energyInclusion_coe,poincareEnergySeed_value] using hh
  have hval : (energyInclusion N U).val=hfP.toLp (poincareSum (G := gamma N) (upperFunction f)) :=
    tendsto_nhds_unique htv ht
  refine ⟨u,U,hval.trans ?_,hU,ha,K,hK,hs⟩
  apply Lp.ext
  filter_upwards [hfP.coeFn_toLp,poincareSeedVector_coeFn N w,
    AsymptoticL2Multiplier.operator_coeFn (fun z => (weight N ε v z:ℂ))
      (Complex.measurable_ofReal.comp (weight_measurable N ε v)).aestronglyMeasurable
      (Eventually.of_forall (quotientWeight_complex_bound N hε hv)) (poincareSeedVector N w).val]
    with z hz hw hb
  change _=quotientWeightMultiplier N hε hv (poincareSeedVector N w).val z
  change quotientWeightMultiplier N hε hv (poincareSeedVector N w).val z=
    (weight N ε v z:ℂ)*(poincareSeedVector N w).val z at hb
  rw [hz,hb,hw,hfU]
  exact poincareSum_mul_invariant (upperFunction w.toFun) (fun z => (weight N ε v z:ℂ))
    (fun g z => congrArg Complex.ofReal (weight_invariant N ε v g z)) z

theorem quotientWeight_seed_energy_value (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    ∃ U : QuotientEnergySpace N,
      (energyInclusion N U).val=quotientWeightMultiplier N hε hv (poincareSeedVector N w).val := by
  obtain ⟨u,U,hvalue,_⟩ := quotientWeight_seed_energy_realization N hε hv w
  exact ⟨U,hvalue⟩

#print axioms quotientWeight_seed_energy_realization
#print axioms quotientWeight_seed_energy_value

end QuantitativeMaass
