module

public import QuantitativeMaassInverseMetricBranchV1
public import QuantitativeHolomorphicReconstructionMatrixV1
public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap MeasureTheory Filter UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson QuantitativeHolomorphic
namespace QuantitativeMaass

private theorem selfAdjoint_intertwining_compression
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (J : H→ₗᵢ[ℂ]G) (B F : G→L[ℂ]G) (D : H→L[ℂ]H)
    (hB : B.adjoint=B) (h : B.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D) :
    J.toContinuousLinearMap.adjoint.comp ((B.comp (F.comp B.adjoint)).comp J.toContinuousLinearMap)=
      D.comp ((J.toContinuousLinearMap.adjoint.comp (F.comp J.toContinuousLinearMap)).comp D.adjoint) := by
  let Z := J.toContinuousLinearMap
  change B.comp Z=Z.comp D at h
  have hZ : Z.adjoint.comp Z=1 := J.adjoint_comp_self
  have hd : Z.adjoint.comp (B.comp Z)=D := by
    rw [h,←comp_assoc,hZ]
    rfl
  have hDs : D.adjoint=D := by
    rw [←hd]
    simp only [adjoint_comp,adjoint_adjoint,hB,comp_assoc]
  have ha := congrArg (fun T : H→L[ℂ]G => T.adjoint) h
  simp only [adjoint_comp,hB,hDs] at ha
  change Z.adjoint.comp ((B.comp (F.comp B.adjoint)).comp Z)=_
  rw [hB,hDs]
  calc
    _ = (Z.adjoint.comp B).comp (F.comp (B.comp Z)) := by simp only [comp_assoc]
    _ = (D.comp Z.adjoint).comp (F.comp (Z.comp D)) := by rw [ha,h]
    _ = _ := by simp only [comp_assoc]; rfl

namespace ScalarCylinderMetric
variable {N : ℕ} (M : ScalarCylinderMetric N)

theorem physicalInverse_adjoint :
    M.physicalChange.symm.toContinuousLinearMap.adjoint=M.physicalChange.symm.toContinuousLinearMap := by
  exact AsymptoticL2Multiplier.operator_adjoint (fun z => ((M.weight z)⁻¹:ℝ))
    (Complex.measurable_ofReal.comp M.measurable.inv).aestronglyMeasurable
    (Eventually.of_forall M.inverse_complex_bound)
    (Eventually.of_forall (fun z => by simp only [Complex.star_def,Complex.conj_ofReal]))

theorem inverseBranch_intertwines :
    (holomorphicSum [M.inverseBranch] 0).comp cylinderZeroExtension.toContinuousLinearMap=
      cylinderZeroExtension.toContinuousLinearMap.comp M.change.symm.toContinuousLinearMap := by
  rw [M.inverseBranch_physical]
  apply ContinuousLinearMap.ext
  intro f
  apply M.physicalChange.injective
  change M.physicalChange (M.physicalChange.symm (cylinderZeroExtension f))=
    M.physicalChange (cylinderZeroExtension (M.change.symm f))
  rw [M.physicalChange.apply_symm_apply,M.physicalChange_zeroExtension,M.change.apply_symm_apply]

/-- The inverse metric is inserted as the same finite branch expression in
both representations. -/
def inverseSandwich (E : Expression) : Expression :=
  composeExpression [M.inverseBranch] (composeExpression E (adjointExpression [M.inverseBranch]))

theorem inverseSandwich_physical (E : Expression) :
    holomorphicSum (M.inverseSandwich E) 0=
      M.physicalChange.symm.toContinuousLinearMap.comp
        ((holomorphicSum E 0).comp M.physicalChange.symm.toContinuousLinearMap.adjoint) := by
  simp only [inverseSandwich,holomorphicSum_compose,holomorphicSum_adjoint,M.inverseBranch_physical]

theorem inverseSandwich_regular (E : Expression) (z : ℍ) :
    regularSum (M.inverseSandwich E) z=
      (M.regularChange z).symm.toContinuousLinearMap.comp
        ((regularSum E z).comp (M.regularChange z).symm.toContinuousLinearMap.adjoint) := by
  simp only [inverseSandwich,regularSum_compose,regularSum_adjoint,M.inverseBranch_regular]

theorem inverseSandwich_cylinder (E : Expression) :
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let D := M.change.symm.toContinuousLinearMap
    Z.adjoint.comp ((holomorphicSum (M.inverseSandwich E) 0).comp Z)=
      D.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp D.adjoint) := by
  intro Z D
  rw [M.inverseSandwich_physical]
  apply selfAdjoint_intertwining_compression cylinderZeroExtension _ _ D M.physicalInverse_adjoint
  rw [←M.inverseBranch_physical]
  exact M.inverseBranch_intertwines

theorem inverseSandwich_matrix (E : Expression) {B : ℝ}
    (hB : 0≤B) (hE : ExpressionMatrixBound E B) :
    ExpressionMatrixBound (M.inverseSandwich E) (4*B) := by
  have hK := expressionMatrixBound_singleton_one M.inverseBranch rfl
  have hh := hK.compose (hE.compose hK.adjoint zero_le_one) (by positivity : 0≤2*B*1)
  convert hh using 1
  · rfl
  · ring

theorem inverseSandwich_mass (E : Expression) :
    expressionBound (M.inverseSandwich E)=(M.lower⁻¹)^2*expressionBound E := by
  rw [inverseSandwich,expressionBound_compose,expressionBound_compose,expressionBound_adjoint]
  have h : expressionBound [M.inverseBranch]=M.lower⁻¹ := by
    simp only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rfl
  rw [h]
  ring

/-- The finite-filter term in the actual count is the cylinder compression
of a literal inverse-metric finite expression. -/
theorem inverseSandwich_columnTrace {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→Lp ℂ 2 (quotientMeasure 0)) (E : Expression) :
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let D := M.change.symm.toContinuousLinearMap
    columnLinearTrace μ c (D.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp D.adjoint))=
      columnLinearTrace μ c (Z.adjoint.comp ((holomorphicSum (M.inverseSandwich E) 0).comp Z)) := by
  intro Z D
  rw [M.inverseSandwich_cylinder]

#print axioms physicalInverse_adjoint
#print axioms inverseBranch_intertwines
#print axioms inverseSandwich_physical
#print axioms inverseSandwich_regular
#print axioms inverseSandwich_cylinder
#print axioms inverseSandwich_matrix
#print axioms inverseSandwich_mass
#print axioms inverseSandwich_columnTrace
end ScalarCylinderMetric
end QuantitativeMaass
