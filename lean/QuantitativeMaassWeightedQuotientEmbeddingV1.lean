module

public import QuantitativeMaassUniformQuotientWeightV1
public import QuantitativeMaassLocalRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open scoped ENNReal

namespace QuantitativeMaass

theorem weightedRepresentative_memLp (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    MemLp (fun z => (cap ε v z:ℂ)*f.val z) 2 (quotientMeasure 0) := by
  have hm : Measurable (fun z => (cap ε v z:ℂ)*f.val z) :=
    (Complex.measurable_ofReal.comp (cap_continuous ε v).measurable).mul f.property.1
  have hi := (memLp_two_iff_integrable_sq_norm f.property.2.2.aestronglyMeasurable).mp f.property.2.2
  have hf : (∫⁻ z,ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N)<∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  have hb := weighted_quotient_energy_uniform N hε hv f.val f.property.1 f.property.2.1
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

def weightedQuotientRepresentative (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      Lp ℂ 2 (quotientMeasure 0) where
  toFun f := (weightedRepresentative_memLp N hε hv f).toLp (fun z => (cap ε v z:ℂ)*f.val z)
  map_add' f g := by
    rw [←MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun z => mul_add (cap ε v z:ℂ) (f.val z) (g.val z))
  map_smul' c f := by
    rw [←MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Eventually.of_forall
    intro z
    change (cap ε v z:ℂ)*(c*f.val z)=c*((cap ε v z:ℂ)*f.val z)
    ring

theorem weightedQuotientRepresentative_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖weightedQuotientRepresentative N hε hv f‖≤(quotientWeightBound ε+1)*
      ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  have hi := (memLp_two_iff_integrable_sq_norm f.property.2.2.aestronglyMeasurable).mp f.property.2.2
  have hf : (∫⁻ z,ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N)≠∞ :=
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2).ne
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf)
    (weighted_quotient_energy_uniform N hε hv f.val f.property.1 f.property.2.1)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (quotientWeightBound_nonneg ε),
    square_energy_toReal _ (weightedRepresentative_memLp N hε hv f),
    square_energy_toReal _ f.property.2.2] at hb
  change ‖weightedQuotientRepresentative N hε hv f‖^2≤quotientWeightBound ε*
    ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖^2 at hb
  have hC := quotientWeightBound_nonneg ε
  have hmul := mul_le_mul_of_nonneg_right
    (show quotientWeightBound ε≤(quotientWeightBound ε+1)^2 by nlinarith)
    (sq_nonneg ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  rw [mul_pow]
  exact hb.trans hmul

/-- The actual bounded cap-weighted quotient-to-cylinder map on the whole
automorphic Hilbert completion. Its upper norm bound has no spectral or
newform assumption. -/
def weightedQuotientEmbedding (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) : AutomorphicSpace N →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (weightedQuotientRepresentative N hε hv).extendOfNorm
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))

theorem weightedQuotientEmbedding_representative (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    weightedQuotientEmbedding N hε hv
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
      weightedQuotientRepresentative N hε hv f :=
  LinearMap.extendOfNorm_eq
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
    ⟨quotientWeightBound ε+1,weightedQuotientRepresentative_bound N hε hv⟩ f

theorem weightedQuotientEmbedding_norm_le (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    ‖weightedQuotientEmbedding N hε hv‖≤quotientWeightBound ε+1 := by
  apply LinearMap.opNorm_extendOfNorm_le
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
    (by linarith [quotientWeightBound_nonneg ε])
  exact weightedQuotientRepresentative_bound N hε hv

#print axioms weightedRepresentative_memLp
#print axioms weightedQuotientRepresentative_bound
#print axioms weightedQuotientEmbedding_representative
#print axioms weightedQuotientEmbedding_norm_le

end QuantitativeMaass
