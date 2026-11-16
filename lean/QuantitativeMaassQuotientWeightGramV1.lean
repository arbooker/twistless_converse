module

public import QuantitativeMaassQuotientWeightRootV1
public import QuantitativeMaassMultiplierAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceWeight AsymptoticClassicalPetersson

namespace QuantitativeMaass

theorem gram_eq_of_norm_eq {E H K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : E →L[ℂ] H) (S : E →L[ℂ] K) (h : ∀ x,‖R x‖=‖S x‖) :
    R.adjoint.comp R=S.adjoint.comp S := by
  have heq : (R.adjoint.comp R).toLinearMap=(S.adjoint.comp S).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro x
    change inner ℂ (R.adjoint (R x)) x=inner ℂ (S.adjoint (S x)) x
    rw [R.adjoint_inner_left,S.adjoint_inner_left,inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K,h x]
  ext x
  exact LinearMap.congr_fun heq x

theorem quotientWeight_complex_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z : ℍ) : ‖(weight N ε v z:ℂ)‖≤quotientWeightBound ε := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (quotientWeight_nonneg N ε v z)]
  exact quotientWeight_uniform_bound N hε hv z

def quotientWeightMultiplier (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  AsymptoticL2Multiplier.operator (fun z => (weight N ε v z:ℂ))
    (Complex.measurable_ofReal.comp (weight_measurable N ε v)).aestronglyMeasurable
    (Eventually.of_forall (quotientWeight_complex_bound N hε hv))

theorem quotientWeightRootMultiplier_adjoint (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    (quotientWeightRootMultiplier N hε hv).adjoint=quotientWeightRootMultiplier N hε hv :=
  AsymptoticL2Multiplier.operator_adjoint _ _ _ (Eventually.of_forall (fun _ => by simp))

theorem quotientWeightRootMultiplier_square (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    (quotientWeightRootMultiplier N hε hv).comp (quotientWeightRootMultiplier N hε hv)=
      quotientWeightMultiplier N hε hv := by
  ext f : 1
  apply Lp.ext
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn
      (fun z => (Real.sqrt (weight N ε v z):ℂ))
      (quotientWeightRoot_measurable N ε v).aestronglyMeasurable
      (Eventually.of_forall (quotientWeightRoot_bound N hε hv))
      (quotientWeightRootMultiplier N hε hv f),
    AsymptoticL2Multiplier.operator_coeFn
      (fun z => (Real.sqrt (weight N ε v z):ℂ))
      (quotientWeightRoot_measurable N ε v).aestronglyMeasurable
      (Eventually.of_forall (quotientWeightRoot_bound N hε hv)) f,
    AsymptoticL2Multiplier.operator_coeFn (fun z => (weight N ε v z:ℂ))
      (Complex.measurable_ofReal.comp (weight_measurable N ε v)).aestronglyMeasurable
      (Eventually.of_forall (quotientWeight_complex_bound N hε hv)) f] with z h1 h2 h3
  change quotientWeightRootMultiplier N hε hv (quotientWeightRootMultiplier N hε hv f) z=
    quotientWeightMultiplier N hε hv f z
  change quotientWeightRootMultiplier N hε hv (quotientWeightRootMultiplier N hε hv f) z=
    (Real.sqrt (weight N ε v z):ℂ)*quotientWeightRootMultiplier N hε hv f z at h1
  change quotientWeightRootMultiplier N hε hv f z=
    (Real.sqrt (weight N ε v z):ℂ)*f z at h2
  change quotientWeightMultiplier N hε hv f z=(weight N ε v z:ℂ)*f z at h3
  rw [h1,h2,h3,←mul_assoc]
  congr 1
  exact_mod_cast Real.mul_self_sqrt (quotientWeight_nonneg N ε v z)

/-- The literal capped cylinder embedding has the actual orbit-weight
multiplier as its quotient Gram operator. This identifies the weight
without asserting the differentiability needed for cutoff localization. -/
theorem weightedQuotientEmbedding_gram (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    (weightedQuotientEmbedding N hε hv).adjoint.comp (weightedQuotientEmbedding N hε hv)=
      (AutomorphicSpace N).subtypeL.adjoint.comp
        ((quotientWeightMultiplier N hε hv).comp (AutomorphicSpace N).subtypeL) := by
  rw [gram_eq_of_norm_eq (weightedQuotientEmbedding N hε hv)
    (quotientWeightRootEmbedding N hε hv) (quotientWeightRoot_norm N hε hv)]
  unfold quotientWeightRootEmbedding
  rw [ContinuousLinearMap.adjoint_comp,quotientWeightRootMultiplier_adjoint]
  ext f : 1
  change (AutomorphicSpace N).subtypeL.adjoint
    (quotientWeightRootMultiplier N hε hv
      (quotientWeightRootMultiplier N hε hv ((AutomorphicSpace N).subtypeL f))) = _
  exact congrArg (AutomorphicSpace N).subtypeL.adjoint
    (DFunLike.congr_fun (quotientWeightRootMultiplier_square N hε hv)
      ((AutomorphicSpace N).subtypeL f))

#print axioms gram_eq_of_norm_eq
#print axioms quotientWeight_complex_bound
#print axioms quotientWeightRootMultiplier_adjoint
#print axioms quotientWeightRootMultiplier_square
#print axioms weightedQuotientEmbedding_gram

end QuantitativeMaass
