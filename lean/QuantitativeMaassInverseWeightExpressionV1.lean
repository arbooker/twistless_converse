module

public import QuantitativeMaassCappedColumnTraceV1
public import QuantitativeMaassCylinderPhysicalV1
public import QuantitativeHolomorphicReconstructionMatrixV1
public import QuantitativeMaassWeightBandGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson QuantitativeHolomorphic
namespace QuantitativeMaass

def inverseWeightBranch (ε : ℝ) (m : ℕ) (n : ℤ) : Branch where
  label := 1
  coefficient := LogBands.inverseCoefficient (fun z => Real.log (cappedHeightWeight ε m z)) n
  measurable := LogBands.inverseCoefficient_measurable _ (cappedHeightWeight_log_measurable ε m) n
  bound := Real.exp (-(n:ℝ))
  bound_nonneg := (Real.exp_pos _).le
  norm_le := LogBands.inverseCoefficient_bound _ n

def terminalInverseWeightExpression (ε : ℝ) (m J : ℕ) : Expression :=
  sumExpressions (Finset.Icc (-(J:ℤ)) J) (fun n => [inverseWeightBranch ε m n])

/-- Each inverse-band multiplier is an actual identity-labelled rational
branch on the physical ambient space, with the correct cylinder restriction. -/
theorem inverseWeightBranch_intertwines (ε : ℝ) (m : ℕ) (n : ℤ) :
    (holomorphic (inverseWeightBranch ε m n) 0).comp cylinderZeroExtension.toContinuousLinearMap=
      cylinderZeroExtension.toContinuousLinearMap.comp
        (LogBands.inverse (quotientMeasure 0) (fun z => Real.log (cappedHeightWeight ε m z))
          (cappedHeightWeight_log_measurable ε m) n) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hi := LogBands.inverse_coeFn (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε m z)) (cappedHeightWeight_log_measurable ε m) n f
  have hz := cylinderZeroExtension_coeFn_of_ae _ _ hi
  have hb := AsymptoticConcreteRationalBranch.operator_coeFn
    (inverseWeightBranch ε m n).label (inverseWeightBranch ε m n).coefficient
    (inverseWeightBranch ε m n).measurable (inverseWeightBranch ε m n).norm_le 0
    (cylinderZeroExtension f)
  filter_upwards [hb,hz,cylinderZeroExtension_coeFn f] with z hb hz hf
  change holomorphic (inverseWeightBranch ε m n) 0 (cylinderZeroExtension f) z=_ at hb
  change holomorphic (inverseWeightBranch ε m n) 0 (cylinderZeroExtension f) z=
    cylinderZeroExtension
      (LogBands.inverse (quotientMeasure 0) (fun z => Real.log (cappedHeightWeight ε m z))
        (cappedHeightWeight_log_measurable ε m) n f) z
  rw [hb,hz]
  change (inverseWeightBranch ε m n).coefficient z*AsymptoticSlashGauge.phase 1 0 z*
    cylinderZeroExtension f (1 • z)=_
  rw [AsymptoticSlashGauge.phase_one,mul_one,one_smul,hf]
  classical
  by_cases hzs : z∈AsymptoticMassTransport.strip
  · rw [indicator_of_mem hzs,indicator_of_mem hzs]
    rfl
  · rw [indicator_of_notMem hzs,indicator_of_notMem hzs,mul_zero]

/-- The bounded inverse cap is the same literal finite expression in the
physical and regular representation, before any trace estimates are invoked. -/
theorem terminalInverseWeightExpression_intertwines (ε : ℝ) (m J : ℕ) :
    (holomorphicSum (terminalInverseWeightExpression ε m J) 0).comp
      cylinderZeroExtension.toContinuousLinearMap=
      cylinderZeroExtension.toContinuousLinearMap.comp (terminalInverseWeightBand ε m J) := by
  rw [terminalInverseWeightExpression,holomorphicSum_sumExpressions]
  apply ContinuousLinearMap.ext
  intro f
  simp only [comp_apply,sum_apply,terminalInverseWeightBand,LogBands.rowInverseSum,
    zero_sub,zero_add,holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact DFunLike.congr_fun (inverseWeightBranch_intertwines ε m n) f

/-- No nonidentity geometric label is introduced by the bounded inverse cap. -/
theorem terminalInverseWeightExpression_matrix (ε : ℝ) (m J : ℕ) :
    ExpressionMatrixBound (terminalInverseWeightExpression ε m J) 1 := by
  apply expressionMatrixBound_sum
  intro n _
  exact expressionMatrixBound_singleton_one (inverseWeightBranch ε m n) rfl

/-- The explicit coefficient mass is at most one exponential in the
propagation band. This is independent of the spectral center. -/
theorem terminalInverseWeightExpression_mass (ε : ℝ) (m J : ℕ) :
    expressionBound (terminalInverseWeightExpression ε m J)≤
      ((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1) := by
  classical
  rw [terminalInverseWeightExpression,expressionBound_sumExpressions]
  simp only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change (∑ n∈Finset.Icc (-(J:ℤ)) J,Real.exp (-(n:ℝ)))≤_
  calc
    _≤∑ _n∈Finset.Icc (-(J:ℤ)) J,Real.exp ((J:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Real.exp_le_exp.mpr
      have hlow : -(J:ℝ)≤(n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      linarith
    _=_ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard := integer_band_card J 0
      simp only [zero_sub,zero_add] at hcard
      rw [hcard]

#print axioms inverseWeightBranch_intertwines
#print axioms terminalInverseWeightExpression_intertwines
#print axioms terminalInverseWeightExpression_matrix
#print axioms terminalInverseWeightExpression_mass
end QuantitativeMaass
