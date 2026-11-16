module

public import QuantitativeMaassScalarMetricPacketV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticFiniteBranch AsymptoticCongruenceStrip
namespace QuantitativeMaass

theorem ScalarCylinderMetric.complex_bound {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) :
    ‖(M.weight z:ℂ)‖≤M.upper := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (M.lower_pos.le.trans (M.bounds z).1)]
  exact (M.bounds z).2

def ScalarCylinderMetric.quotientMultiplier {N : ℕ} (M : ScalarCylinderMetric N) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  invariantQuotientMultiplier N (fun z => (M.weight z:ℂ))
    (Complex.measurable_ofReal.comp M.measurable)
    (fun a z => congrArg Complex.ofReal (M.invariant a z)) M.complex_bound

theorem ScalarCylinderMetric.quotientMultiplier_adjoint {N : ℕ} (M : ScalarCylinderMetric N) :
    M.quotientMultiplier.adjoint=M.quotientMultiplier := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℂ (M.quotientMultiplier f).val g.val=
    inner ℂ f.val (M.quotientMultiplier g).val
  simp only [ScalarCylinderMetric.quotientMultiplier,invariantQuotientMultiplier_value]
  have ha := AsymptoticL2Multiplier.operator_adjoint
    (μ:=quotientMeasure N) (fun z => (M.weight z:ℂ))
    (Complex.measurable_ofReal.comp M.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall M.complex_bound)
    (Filter.Eventually.of_forall (fun _ => by simp))
  simpa only [ha] using (AsymptoticL2Multiplier.operator
    (μ:=quotientMeasure N) (fun z => (M.weight z:ℂ))
    (Complex.measurable_ofReal.comp M.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall M.complex_bound)).adjoint_inner_left g.val f.val

theorem ScalarCylinderMetric.embedding_eq {N : ℕ} (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    scalarMetricQuotientEmbedding N M hδ hν=
      (weightedQuotientEmbedding N hδ hν).comp M.quotientMultiplier := by
  apply ContinuousLinearMap.ext
  intro x
  change M.change (weightedQuotientEmbedding N hδ hν x)=_
  simp only [ContinuousLinearMap.comp_apply,ScalarCylinderMetric.quotientMultiplier]
  rw [invariantMultiplier_weighted_embedding]
  apply Lp.ext
  exact (M.coeFn _).trans (AsymptoticL2Multiplier.operator_coeFn _ _ _ _).symm

/-- The full transformed Gram has just one invariant multiplication weight.
No cusp projection is suppressed and no multiplier is commuted with waves. -/
theorem ScalarCylinderMetric.gram {N : ℕ} (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    (scalarMetricQuotientEmbedding N M hδ hν).adjoint.comp
      (scalarMetricQuotientEmbedding N M hδ hν)=
      M.quotientMultiplier.comp ((quotientWeightAutomorphicMultiplier N hδ hν).comp
        M.quotientMultiplier) := by
  rw [M.embedding_eq hδ hν,ContinuousLinearMap.adjoint_comp,M.quotientMultiplier_adjoint]
  have hg := weightedQuotientEmbedding_gram_automorphic N hδ hν
  apply ContinuousLinearMap.ext
  intro x
  change M.quotientMultiplier ((weightedQuotientEmbedding N hδ hν).adjoint
    (weightedQuotientEmbedding N hδ hν (M.quotientMultiplier x)))=_
  rw [show (weightedQuotientEmbedding N hδ hν).adjoint
      (weightedQuotientEmbedding N hδ hν (M.quotientMultiplier x))=
      quotientWeightAutomorphicMultiplier N hδ hν (M.quotientMultiplier x) from
    DFunLike.congr_fun hg (M.quotientMultiplier x)]
  rfl

def ScalarCylinderMetric.branch {N : ℕ} (M : ScalarCylinderMetric N) : Branch where
  label := 1
  coefficient z := (M.weight z:ℂ)
  measurable := Complex.measurable_ofReal.comp M.measurable
  bound := M.upper
  bound_nonneg := M.lower_pos.le.trans ((M.bounds ⟨Complex.I,by simp⟩).1.trans
    (M.bounds ⟨Complex.I,by simp⟩).2)
  norm_le := M.complex_bound

theorem ScalarCylinderMetric.realizes {N : ℕ} (M : ScalarCylinderMetric N) :
    QuotientRealizes N [M.branch] M.quotientMultiplier := by
  intro f
  refine ⟨invariantMultiplierRepresentative N (fun z => (M.weight z:ℂ))
    (Complex.measurable_ofReal.comp M.measurable)
    (fun a z => congrArg Complex.ofReal (M.invariant a z)) M.complex_bound f,?_,?_⟩
  · exact (invariantQuotientMultiplier_representative _ _ _ _ _ f).symm
  · ext z
    simp [expressionFunction,branchFunction,ScalarCylinderMetric.branch,
      invariantMultiplierRepresentative]

def ScalarCylinderMetric.gramExpression {N : ℕ} (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) : Expression :=
  composeExpression [M.branch] (composeExpression [quotientWeightBranch N hδ hν] [M.branch])

theorem ScalarCylinderMetric.gram_realizes {N : ℕ} (M : ScalarCylinderMetric N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) :
    QuotientRealizes N (M.gramExpression hδ hν)
      ((scalarMetricQuotientEmbedding N M hδ hν).adjoint.comp
        (scalarMetricQuotientEmbedding N M hδ hν)) := by
  rw [M.gram hδ hν]
  exact M.realizes.mul ((quotientWeight_realizes N hδ hν).mul M.realizes)

#print axioms ScalarCylinderMetric.quotientMultiplier_adjoint
#print axioms ScalarCylinderMetric.embedding_eq
#print axioms ScalarCylinderMetric.gram
#print axioms ScalarCylinderMetric.realizes
#print axioms ScalarCylinderMetric.gram_realizes
end QuantitativeMaass
