module

public import QuantitativeMaassInverseMetricExpressionV1
public import QuantitativeMaassCappedExcessExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson QuantitativeHolomorphic
namespace QuantitativeMaass

private theorem selfAdjoint_sandwich_intertwines
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (Z : H→L[ℂ]G) (B F : G→L[ℂ]G) (K : H→L[ℂ]H)
    (hB : B.adjoint=B) (hK : K.adjoint=K) (h : B.comp Z=Z.comp K) :
    Z.adjoint.comp ((B.comp (F.comp B.adjoint)).comp Z)=
      K.comp ((Z.adjoint.comp (F.comp Z)).comp K.adjoint) := by
  have ha := congrArg (fun T : H→L[ℂ]G => T.adjoint) h
  simp only [adjoint_comp,hB,hK] at ha
  rw [hB,hK]
  calc
    _ = (Z.adjoint.comp B).comp (F.comp (B.comp Z)) := by simp only [comp_assoc]
    _ = (K.comp Z.adjoint).comp (F.comp (Z.comp K)) := by rw [ha,h]
    _ = _ := by simp only [comp_assoc]

private theorem compose_sandwich {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K D T : H→L[ℂ]H) :
    K.comp ((D.comp (T.comp D.adjoint)).comp K.adjoint)=
      (K.comp D).comp (T.comp (K.comp D).adjoint) := by
  simp only [adjoint_comp,comp_assoc]

theorem LogBands.inverse_adjoint_real {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (l : α→ℝ) (hl : Measurable l) (n : ℤ) :
    (LogBands.inverse μ l hl n).adjoint=LogBands.inverse μ l hl n := by
  apply AsymptoticL2Multiplier.operator_adjoint
  apply Eventually.of_forall
  intro x
  classical
  by_cases hx : x∈LogBands.region l n
  · simp only [LogBands.inverseCoefficient,indicator_of_mem hx,Complex.star_def,Complex.conj_ofReal]
  · simp only [LogBands.inverseCoefficient,indicator_of_notMem hx,star_zero]

theorem terminalInverseWeightBand_adjoint (ε : ℝ) (m J : ℕ) :
    (terminalInverseWeightBand ε m J).adjoint=terminalInverseWeightBand ε m J := by
  simp only [terminalInverseWeightBand,LogBands.rowInverseSum,map_sum,LogBands.inverse_adjoint_real]

theorem terminalInverseWeightExpression_volume (ε : ℝ) (m J : ℕ) :
    holomorphicSum (terminalInverseWeightExpression ε m J) 0=
      LogBands.rowInverseSum volume (fun z => Real.log (cappedHeightWeight ε m z))
        (cappedHeightWeight_log_measurable ε m) J 0 := by
  rw [terminalInverseWeightExpression,holomorphicSum_sumExpressions]
  simp only [LogBands.rowInverseSum,zero_sub,zero_add,holomorphicSum,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]
  apply Finset.sum_congr rfl
  intro n _
  change AsymptoticConcreteRationalBranch.operator 1 _ _ _ 0=_
  rw [AsymptoticConcreteRationalBranch.operator_one_label]
  rfl

theorem terminalInverseWeightExpression_adjoint (ε : ℝ) (m J : ℕ) :
    (holomorphicSum (terminalInverseWeightExpression ε m J) 0).adjoint=
      holomorphicSum (terminalInverseWeightExpression ε m J) 0 := by
  rw [terminalInverseWeightExpression_volume]
  simp only [LogBands.rowInverseSum,map_sum,LogBands.inverse_adjoint_real]

/-- The finite inverse cap commutes with cylinder compression in exactly
the sandwich used by the compact-input excess trace. -/
theorem cappedSandwichExpression_cylinder (ε : ℝ) (m J : ℕ) (E : Expression) :
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let K := terminalInverseWeightBand ε m J
    Z.adjoint.comp ((holomorphicSum (cappedSandwichExpression ε m J E) 0).comp Z)=
      K.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp K.adjoint) := by
  intro Z K
  have hh := selfAdjoint_sandwich_intertwines Z
    (holomorphicSum (terminalInverseWeightExpression ε m J) 0) (holomorphicSum E 0) K
    (terminalInverseWeightExpression_adjoint ε m J) (terminalInverseWeightBand_adjoint ε m J)
    (terminalInverseWeightExpression_intertwines ε m J)
  exact (congrArg (fun T : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space =>
    Z.adjoint.comp (T.comp Z)) (cappedSandwichExpression_physical ε m J E)).trans hh

/-- A literal finite expression for both inverse metric and inverse cap. -/
def metricCappedExpression {N : ℕ} (M : ScalarCylinderMetric N)
    (ε : ℝ) (m J : ℕ) (E : Expression) : Expression :=
  cappedSandwichExpression ε m J (M.inverseSandwich E)

theorem metricCappedExpression_cylinder {N : ℕ} (M : ScalarCylinderMetric N)
    (ε : ℝ) (m J : ℕ) (E : Expression) :
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let L := (terminalInverseWeightBand ε m J).comp M.change.symm.toContinuousLinearMap
    Z.adjoint.comp ((holomorphicSum (metricCappedExpression M ε m J E) 0).comp Z)=
      L.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp L.adjoint) := by
  intro Z L
  let K := terminalInverseWeightBand ε m J
  let D := M.change.symm.toContinuousLinearMap
  have hcap := cappedSandwichExpression_cylinder ε m J (M.inverseSandwich E)
  have hinv := M.inverseSandwich_cylinder E
  have hh := congrArg (fun T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) =>
    K.comp (T.comp K.adjoint)) hinv
  exact hcap.trans (hh.trans (compose_sandwich K D (Z.adjoint.comp ((holomorphicSum E 0).comp Z))))

theorem metricCappedExpression_matrix {N : ℕ} (M : ScalarCylinderMetric N)
    (ε : ℝ) (m J : ℕ) (E : Expression) {B : ℝ} (hB : 0≤B) (hE : ExpressionMatrixBound E B) :
    ExpressionMatrixBound (metricCappedExpression M ε m J E) (16*B) := by
  have hh := cappedSandwichExpression_matrix ε m J (M.inverseSandwich E)
    (by positivity : 0≤4*B) (M.inverseSandwich_matrix E hB hE)
  convert hh using 1
  · rfl
  · ring

theorem metricCappedExpression_mass {N : ℕ} (M : ScalarCylinderMetric N)
    (ε : ℝ) (m J : ℕ) (E : Expression) :
    expressionBound (metricCappedExpression M ε m J E)≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*(M.lower⁻¹)^2*expressionBound E := by
  have hh := cappedSandwichExpression_mass ε m J (M.inverseSandwich E)
  rw [M.inverseSandwich_mass] at hh
  simpa only [metricCappedExpression,mul_assoc] using hh

#print axioms LogBands.inverse_adjoint_real
#print axioms terminalInverseWeightBand_adjoint
#print axioms terminalInverseWeightExpression_volume
#print axioms terminalInverseWeightExpression_adjoint
#print axioms cappedSandwichExpression_cylinder
#print axioms metricCappedExpression_cylinder
#print axioms metricCappedExpression_matrix
#print axioms metricCappedExpression_mass
end QuantitativeMaass
