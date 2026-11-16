module

public import QuantitativeMaassQuotientGeneratorExpressionV1
public import QuantitativeMaassQuotientWeightContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticFiniteBranch
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
namespace QuantitativeMaass

/-- The orbit weight is a single identity branch with its actual measurable
coefficient, rather than a formal scalar replacing that coefficient. -/
def quotientWeightBranch (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) : Branch where
  label := 1
  coefficient z := (weight N δ ν z:ℂ)
  measurable := Complex.measurable_ofReal.comp (weight_measurable N δ ν)
  bound := quotientWeightBound δ
  bound_nonneg := quotientWeightBound_nonneg δ
  norm_le := quotientWeight_complex_bound N hδ hν

def quotientWeightRepresentative (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  ⟨fun z => (weight N δ ν z:ℂ)*f.val z,
    (Complex.measurable_ofReal.comp (weight_measurable N δ ν)).mul f.property.1,
    by intro g z; dsimp only; rw [weight_invariant,f.property.2.1],
    f.property.2.2.of_le_mul (c:=quotientWeightBound δ)
      (((Complex.measurable_ofReal.comp (weight_measurable N δ ν)).mul f.property.1).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (quotientWeight_complex_bound N hδ hν z) (norm_nonneg _)))⟩

theorem quotientWeightRepresentative_embedding (N : ℕ) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.denseEmbedding _ _ (quotientWeightRepresentative N hδ hν f)=
      quotientWeightAutomorphicMultiplier N hδ hν (AutomorphicL2.denseEmbedding _ _ f) := by
  apply Subtype.ext
  rw [quotientWeightAutomorphicMultiplier_value]
  apply Lp.ext
  filter_upwards [(quotientWeightRepresentative N hδ hν f).property.2.2.coeFn_toLp,
    f.property.2.2.coeFn_toLp,
    AsymptoticL2Multiplier.operator_coeFn (fun z => (weight N δ ν z:ℂ))
      (Complex.measurable_ofReal.comp (weight_measurable N δ ν)).aestronglyMeasurable
      (Filter.Eventually.of_forall (quotientWeight_complex_bound N hδ hν))
      (AutomorphicL2.denseEmbedding _ _ f).val] with z hg hf hm
  change (quotientWeightRepresentative N hδ hν f).property.2.2.toLp _ z=_
  change quotientWeightMultiplier N hδ hν (AutomorphicL2.denseEmbedding _ _ f).val z=
    (weight N δ ν z:ℂ)*f.property.2.2.toLp _ z at hm
  rw [hg,hm,hf]
  rfl

theorem quotientWeight_realizes (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    QuotientRealizes N [quotientWeightBranch N hδ hν]
      (quotientWeightAutomorphicMultiplier N hδ hν) := by
  intro f
  refine ⟨quotientWeightRepresentative N hδ hν f,
    quotientWeightRepresentative_embedding N hδ hν f,?_⟩
  ext z
  simp [expressionFunction,branchFunction,quotientWeightBranch,quotientWeightRepresentative]

/-- The full quotient Gram normalized by the same scalar as the finite bands.
It is not asserted to preserve the cusp subspace. -/
def normalizedQuotientWeight (N : ℕ) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  (quotientWeightNormalization δ:ℂ) • quotientWeightAutomorphicMultiplier N hδ hν

def normalizedQuotientWeightExpression (N : ℕ) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) : Expression :=
  scaleExpression (quotientWeightNormalization δ:ℂ) [quotientWeightBranch N hδ hν]

theorem normalizedQuotientWeight_realizes (N : ℕ) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) :
    QuotientRealizes N (normalizedQuotientWeightExpression N hδ hν)
      (normalizedQuotientWeight N hδ hν) :=
  (quotientWeight_realizes N hδ hν).smul _

theorem normalizedQuotientWeight_norm (N : ℕ) {δ : ℝ} (hδ : 0<δ)
    {ν : ℕ} (hν : 1≤ν) : ‖normalizedQuotientWeight N hδ hν‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(quotientWeightNormalization δ:ℂ) • quotientWeightAutomorphicMultiplier N hδ hν x‖≤1*‖x‖
  rw [norm_smul,quotientWeightNormalization_complex_norm]
  have hb := (quotientWeightAutomorphicMultiplier N hδ hν).le_of_opNorm_le
    (quotientWeightAutomorphicMultiplier_norm N hδ hν) x
  have he : quotientWeightNormalization δ*(quotientWeightBound δ+1)=1 :=
    inv_mul_cancel₀ (by linarith [quotientWeightBound_nonneg δ] : quotientWeightBound δ+1≠0)
  have hh := mul_le_mul_of_nonneg_left hb (quotientWeightNormalization_pos δ).le
  have he2 := congrArg (fun a : ℝ => a*‖x‖) he
  nlinarith [mul_nonneg (quotientWeightNormalization_pos δ).le (norm_nonneg x)]

#print axioms quotientWeightRepresentative_embedding
#print axioms quotientWeight_realizes
#print axioms normalizedQuotientWeight_realizes
#print axioms normalizedQuotientWeight_norm
end QuantitativeMaass
