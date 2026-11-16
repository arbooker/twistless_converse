module

public import QuantitativeMaassWeightedQuotientEmbeddingV1
public import QuantitativeMaassColumnInputTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open AsymptoticCompactBranch AsymptoticCongruenceStrip
open scoped ENNReal

namespace QuantitativeMaass

theorem quotientWeight_nonneg (N : ℕ) (ε : ℝ) (v : ℕ) (z : ℍ) :
    0≤weight N ε v z :=
  tsum_nonneg (fun _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)

theorem quotientWeightRoot_measurable (N : ℕ) (ε : ℝ) (v : ℕ) :
    Measurable (fun z => (Real.sqrt (weight N ε v z):ℂ)) :=
  Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp (weight_measurable N ε v))

theorem quotientWeightRoot_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z : ℍ) :
    ‖(Real.sqrt (weight N ε v z):ℂ)‖≤Real.sqrt (quotientWeightBound ε) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (quotientWeight_uniform_bound N hε hv z)

/-- The actual square-root orbit weight acts on quotient L2. Smoothness
is not asserted: the capped weight is only used as a bounded measurable function. -/
def quotientWeightRootMultiplier (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  AsymptoticL2Multiplier.operator (fun z => (Real.sqrt (weight N ε v z):ℂ))
    (quotientWeightRoot_measurable N ε v).aestronglyMeasurable
    (Eventually.of_forall (quotientWeightRoot_bound N hε hv))

def quotientWeightRootEmbedding (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : AutomorphicSpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  (quotientWeightRootMultiplier N hε hv).comp (AutomorphicSpace N).subtypeL

/-- Exact equality of the cylinder-weighted and orbit-weighted norms on
every automorphic representative, from the proved unfolding identity. -/
theorem quotientWeightRoot_representative_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖weightedQuotientEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ f)‖=
      ‖quotientWeightRootEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ f)‖ := by
  have hR : ENNReal.ofReal (‖weightedQuotientEmbedding N hε hv
      (AutomorphicL2.denseEmbedding _ _ f)‖^2)=
      ∫⁻ z,ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f.val z‖^2)
        ∂quotientMeasure N := by
    rw [weightedQuotientEmbedding_representative,complexLp_norm_square_lintegral]
    rw [←weighted_quotient_energy N hε hv f.val f.property.1 f.property.2.1]
    apply lintegral_congr_ae
    filter_upwards [(weightedRepresentative_memLp N hε hv f).coeFn_toLp] with z hz
    change ENNReal.ofReal (‖(weightedRepresentative_memLp N hε hv f).toLp _ z‖^2)=_
    rw [hz]
  have hS : ENNReal.ofReal (‖quotientWeightRootEmbedding N hε hv
      (AutomorphicL2.denseEmbedding _ _ f)‖^2)=
      ∫⁻ z,ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f.val z‖^2)
        ∂quotientMeasure N := by
    rw [complexLp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [AsymptoticL2Multiplier.operator_coeFn
      (fun z => (Real.sqrt (weight N ε v z):ℂ))
      (quotientWeightRoot_measurable N ε v).aestronglyMeasurable
      (Eventually.of_forall (quotientWeightRoot_bound N hε hv))
      (AutomorphicL2.denseEmbedding _ _ f).val,f.property.2.2.coeFn_toLp] with z hm hf
    change ENNReal.ofReal (‖quotientWeightRootMultiplier N hε hv
      (AutomorphicL2.denseEmbedding _ _ f).val z‖^2)=_
    change quotientWeightRootMultiplier N hε hv (AutomorphicL2.denseEmbedding _ _ f).val z=
      (Real.sqrt (weight N ε v z):ℂ)*(AutomorphicL2.denseEmbedding _ _ f).val z at hm
    rw [hm]
    change ENNReal.ofReal (‖(Real.sqrt (weight N ε v z):ℂ)*f.property.2.2.toLp f.val z‖^2)=_
    rw [hf,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (quotientWeight_nonneg N ε v z),
      ENNReal.ofReal_mul (quotientWeight_nonneg N ε v z)]
  have he := congrArg ENNReal.toReal (hR.trans hS.symm)
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at he
  nlinarith [norm_nonneg (weightedQuotientEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ f)),
    norm_nonneg (quotientWeightRootEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ f))]

/-- The norm identity extends to the full automorphic Hilbert completion. -/
theorem quotientWeightRoot_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (x : AutomorphicSpace N) :
    ‖weightedQuotientEmbedding N hε hv x‖=‖quotientWeightRootEmbedding N hε hv x‖ := by
  have hh : (fun x => ‖weightedQuotientEmbedding N hε hv x‖)=
      (fun x => ‖quotientWeightRootEmbedding N hε hv x‖) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext f
    exact quotientWeightRoot_representative_norm N hε hv f
  exact congrFun hh x

#print axioms quotientWeight_nonneg
#print axioms quotientWeightRoot_bound
#print axioms quotientWeightRoot_representative_norm
#print axioms quotientWeightRoot_norm

end QuantitativeMaass
