module

public import QuantitativeMaassQuotientWeightExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticFiniteBranch
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
namespace QuantitativeMaass

variable (N : ℕ) (c : ℍ→ℂ) (hc : Measurable c)
  (hi : ∀ a : gamma N,∀ z,c (a.val • z)=c z) {C : ℝ} (hC : ∀ z,‖c z‖≤C)

def invariantMultiplierRepresentative :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) where
  toFun f := ⟨fun z => c z*f.val z,hc.mul f.property.1,
    by intro a z; dsimp only; rw [hi,f.property.2.1],
    f.property.2.2.of_le_mul (c:=C) (hc.mul f.property.1).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by rw [norm_mul];exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)))⟩
  map_add' f g := by apply Subtype.ext;ext z;exact mul_add _ _ _
  map_smul' a f := by apply Subtype.ext;ext z;exact mul_left_comm _ _ _

theorem invariantMultiplierRepresentative_bound
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖AutomorphicL2.denseEmbedding _ _ (invariantMultiplierRepresentative N c hc hi hC f)‖≤
      C*‖AutomorphicL2.denseEmbedding _ _ f‖ := by
  change ‖(invariantMultiplierRepresentative N c hc hi hC f).property.2.2.toLp _‖≤
    C*‖f.property.2.2.toLp _‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(invariantMultiplierRepresentative N c hc hi hC f).property.2.2.coeFn_toLp,
    f.property.2.2.coeFn_toLp] with z hg hf
  rw [hg,hf]
  change ‖c z*f.val z‖≤C*‖f.val z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

/-- Literal bounded invariant multiplication on the completed quotient. -/
def invariantQuotientMultiplier : AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  ((AutomorphicL2.denseEmbedding _ _).comp
    (invariantMultiplierRepresentative N c hc hi hC)).extendOfNorm
      (AutomorphicL2.denseEmbedding _ _)

theorem invariantQuotientMultiplier_representative
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    invariantQuotientMultiplier N c hc hi hC (AutomorphicL2.denseEmbedding _ _ f)=
      AutomorphicL2.denseEmbedding _ _ (invariantMultiplierRepresentative N c hc hi hC f) :=
  LinearMap.extendOfNorm_eq (AutomorphicL2.denseEmbedding_dense _ _)
    ⟨C,invariantMultiplierRepresentative_bound N c hc hi hC⟩ f

theorem invariantQuotientMultiplier_norm (hC0 : 0≤C) :
    ‖invariantQuotientMultiplier N c hc hi hC‖≤C :=
  LinearMap.opNorm_extendOfNorm_le (AutomorphicL2.denseEmbedding_dense _ _) hC0
    (invariantMultiplierRepresentative_bound N c hc hi hC)

theorem invariantQuotientMultiplier_value (v : AutomorphicSpace N) :
    (invariantQuotientMultiplier N c hc hi hC v).val=
      AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) v.val := by
  have he : (fun v : AutomorphicSpace N => (invariantQuotientMultiplier N c hc hi hC v).val)=
      fun v => AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) v.val := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    rw [invariantQuotientMultiplier_representative]
    apply Lp.ext
    filter_upwards [(invariantMultiplierRepresentative N c hc hi hC f).property.2.2.coeFn_toLp,
      f.property.2.2.coeFn_toLp,AsymptoticL2Multiplier.operator_coeFn c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) (AutomorphicL2.denseEmbedding _ _ f).val] with z hg hf hm
    change (invariantMultiplierRepresentative N c hc hi hC f).property.2.2.toLp _ z=_
    rw [hg,hm]
    change c z*f.val z=c z*f.property.2.2.toLp _ z
    rw [hf]
  exact congrFun he v

/-- An invariant coefficient may be moved across the literal cap embedding.
This is a multiplier identity, not commutation with a wave operator. -/
theorem invariantMultiplier_weighted_embedding {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (v : AutomorphicSpace N) :
    weightedQuotientEmbedding N hδ hν (invariantQuotientMultiplier N c hc hi hC v)=
      AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) (weightedQuotientEmbedding N hδ hν v) := by
  have he : (fun v => weightedQuotientEmbedding N hδ hν (invariantQuotientMultiplier N c hc hi hC v))=
      fun v => AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) (weightedQuotientEmbedding N hδ hν v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    rw [invariantQuotientMultiplier_representative,weightedQuotientEmbedding_representative,
      weightedQuotientEmbedding_representative]
    apply Lp.ext
    filter_upwards [(weightedRepresentative_memLp N hδ hν
        (invariantMultiplierRepresentative N c hc hi hC f)).coeFn_toLp,
      (weightedRepresentative_memLp N hδ hν f).coeFn_toLp,
      AsymptoticL2Multiplier.operator_coeFn c hc.aestronglyMeasurable
        (Filter.Eventually.of_forall hC) (weightedQuotientRepresentative N hδ hν f)] with z hg hf hm
    rw [hm]
    change (weightedRepresentative_memLp N hδ hν
        (invariantMultiplierRepresentative N c hc hi hC f)).toLp _ z=
      c z*(weightedRepresentative_memLp N hδ hν f).toLp _ z
    rw [hg,hf]
    change (AsymptoticCompactBranch.cap δ ν z:ℂ)*(c z*f.val z)=
      c z*((AsymptoticCompactBranch.cap δ ν z:ℂ)*f.val z)
    ring
  exact congrFun he v

#print axioms invariantMultiplierRepresentative_bound
#print axioms invariantQuotientMultiplier_representative
#print axioms invariantQuotientMultiplier_norm
#print axioms invariantQuotientMultiplier_value
#print axioms invariantMultiplier_weighted_embedding
end QuantitativeMaass
