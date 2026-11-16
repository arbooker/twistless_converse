module

public import QuantitativeMaassQuotientExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticFiniteBranch QuantitativeNinaMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNewGap
namespace QuantitativeMaass

def quotientPullbackBranch (g : AsymptoticRationalGroup.Group) : Branch where
  label := g
  coefficient _ := 1
  measurable := measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le _ := by norm_num

def quotientPullbackExpression (g : AsymptoticRationalGroup.Group) : Expression :=
  [quotientPullbackBranch g]

theorem expressionFunction_pullback (g : AsymptoticRationalGroup.Group) (f : ℍ→ℂ) (z : ℍ) :
    expressionFunction (quotientPullbackExpression g) f z=f (g • z) := by
  simp [expressionFunction,quotientPullbackExpression,branchFunction,quotientPullbackBranch]

theorem quotientNormalizer_realizes (N : ℕ) (g : quotientNormalizerGroup N) :
    QuotientRealizes N (quotientPullbackExpression g.val)
      (quotientNormalizerPullback N g).toContinuousLinearMap := by
  intro f
  refine ⟨quotientNormalizerRepresentative N g f,?_,?_⟩
  · exact (quotientNormalizerPullback_representative N g f).symm
  · ext z
    rw [expressionFunction_pullback]
    rfl

def quotientCoverTraceExpression {M N : ℕ} [NeZero N] (_hMN : M∣N) : Expression :=
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  ofFinset Finset.univ (fun q : gamma M ⧸ (gamma N).subgroupOf (gamma M) =>
    quotientPullbackBranch q.out.val⁻¹)

theorem quotientCoverTrace_realizes {M N : ℕ} [NeZero N] (hMN : M∣N) :
    QuotientRealizes N (quotientCoverTraceExpression hMN)
      ((levelCover hMN).comp (levelTrace hMN)) := by
  intro f
  refine ⟨levelCoverRepresentative hMN (levelTraceRepresentative hMN f),?_,?_⟩
  · rw [←levelCover_apply,←levelTraceRepresentative_embedding]
    rfl
  · ext z
    change (levelTraceRepresentative hMN f).val z=_
    rw [levelTraceRepresentative_apply]
    let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
    change (∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M),f.val (q.out.val⁻¹ • z))=_
    rw [quotientCoverTraceExpression,expressionFunction_ofFinset]
    simp only [LinearMap.sum_apply,Finset.sum_apply,branchFunction,LinearMap.coe_mk,AddHom.coe_mk,
      quotientPullbackBranch,one_mul]

theorem quotientFricke_realizes (N : ℕ) (hN : 0<N) :
    QuotientRealizes N (quotientPullbackExpression (completedFrickeNormalizer N hN).val)
      (frickeIsometry N hN).toContinuousLinearMap :=
  quotientNormalizer_realizes N (completedFrickeNormalizer N hN)

theorem quotientSectorNormalizer_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (i : SectorSignIndex N) :
    QuotientRealizes N (quotientPullbackExpression (sectorNormalizerGroup N hN i).val)
      (completedSectorNormalizer N hN i) := by
  have hh := quotientNormalizer_realizes N (sectorNormalizerGroup N hN i)
  rw [sectorNormalizerGroup_action] at hh
  exact hh

#print axioms quotientNormalizer_realizes
#print axioms quotientCoverTrace_realizes
#print axioms quotientFricke_realizes
#print axioms quotientSectorNormalizer_realizes
end QuantitativeMaass
