module

public import QuantitativeMaassMetricCapExpressionV1
public import QuantitativeMaassLocalRegularWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open QuantitativeHolomorphic
open scoped ComplexConjugate
namespace QuantitativeMaass

def metricCapCoefficient {N : ℕ} (M : ScalarCylinderMetric N) (δ : ℝ) (ν J : ℕ) (z : ℍ) : ℂ :=
  (∑ n ∈ Finset.Icc (-(J:ℤ)) (J:ℤ),
    LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n z)*
    ((M.weight z:ℂ)⁻¹)

theorem metricCapCoefficient_measurable {N : ℕ} (M : ScalarCylinderMetric N) (δ : ℝ) (ν J : ℕ) :
    Measurable (metricCapCoefficient M δ ν J) := by
  apply Measurable.mul
  · exact Finset.measurable_sum _ (fun n _ =>
      LogBands.inverseCoefficient_measurable _ (cappedHeightWeight_log_measurable δ ν) n)
  · exact (Complex.measurable_ofReal.comp M.measurable).inv

theorem metricCapCoefficient_bound {N : ℕ} (M : ScalarCylinderMetric N) (δ : ℝ) (ν J : ℕ) (z : ℍ) :
    ‖metricCapCoefficient M δ ν J z‖≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*M.lower⁻¹ := by
  have hcap : ‖∑ n ∈ Finset.Icc (-(J:ℤ)) (J:ℤ),
      LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n z‖≤
      expressionBound (terminalInverseWeightExpression δ ν J) := by
    rw [terminalInverseWeightExpression,expressionBound_sumExpressions]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n _
    simpa only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,inverseWeightBranch] using
      LogBands.inverseCoefficient_bound (fun u => Real.log (cappedHeightWeight δ ν u)) n z
  have hinv : ‖((M.weight z:ℂ)⁻¹)‖≤M.lower⁻¹ := by
    simpa only [Complex.ofReal_inv] using M.inverse_complex_bound z
  rw [metricCapCoefficient,norm_mul]
  exact mul_le_mul (hcap.trans (terminalInverseWeightExpression_mass δ ν J)) hinv
    (norm_nonneg _) (by positivity)

/-- The inverse metric and inverse cap are diagonal in the same regular
representation. This is their exact matrix action on any finite expression. -/
theorem metricCappedExpression_regular_diagonal {N : ℕ} (M : ScalarCylinderMetric N)
    (δ : ℝ) (ν J : ℕ) (E : Expression) (z : ℍ) :
    matrix (regularSum (metricCappedExpression M δ ν J E) z) 1 1=
      metricCapCoefficient M δ ν J z*conj (metricCapCoefficient M δ ν J z)*
        matrix (regularSum E z) 1 1 := by
  let B := composeExpression (terminalInverseWeightExpression δ ν J) [M.inverseBranch]
  have hB (v : Space) (a : AsymptoticRationalGroup.Group) :
      regularSum B z v a=metricCapCoefficient M δ ν J (a • z)*v a := by
    dsimp only [B]
    rw [regularSum_compose]
    simp only [comp_apply]
    rw [terminalInverseWeightExpression,regularSum_sumExpressions]
    simp only [sum_apply,lp.coeFn_sum,Finset.sum_apply]
    simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    simp only [regular,AsymptoticOrbitBranch.operator_apply,inverseWeightBranch,
      ScalarCylinderMetric.inverseBranch,one_mul]
    simp only [metricCapCoefficient,Complex.ofReal_inv,Finset.sum_mul,mul_assoc]
  have hlow : 0<M.lower := M.lower_pos
  let L := (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*M.lower⁻¹
  let D := AsymptoticOrbitDiagonal.operator
    (fun a : AsymptoticRationalGroup.Group => metricCapCoefficient M δ ν J (a • z))
    (by dsimp only [L]; positivity : 0≤L)
    (fun a => metricCapCoefficient_bound M δ ν J (a • z))
  have hD : regularSum B z=D := by
    ext1 v
    apply lp.ext
    funext a
    exact hB v a
  have heq : regularSum (metricCappedExpression M δ ν J E) z=
      (regularSum B z).comp ((regularSum E z).comp (regularSum B z).adjoint) := by
    simp only [metricCappedExpression,cappedSandwichExpression_regular,
      ScalarCylinderMetric.inverseSandwich,regularSum_compose,regularSum_adjoint,
      B,adjoint_comp,comp_assoc]
  rw [heq,hD]
  simpa only [one_smul,comp_assoc] using
    CountingMetric.diagonal_sandwich_matrix
      (fun a : AsymptoticRationalGroup.Group => metricCapCoefficient M δ ν J (a • z))
      (by dsimp only [L]; positivity : 0≤L)
      (fun a => metricCapCoefficient_bound M δ ν J (a • z)) (regularSum E z) 1 1

/-- The constructed bounded weighted regular excess pays only the explicit
inverse-cap/metric coefficient bound and the scalar window contribution. -/
theorem metric_cap_local_regular_error {N : ℕ} (M : ScalarCylinderMetric N)
    (δ : ℝ) (ν J : ℕ) (F : ℍ→Space→L[ℂ]Space) (E : ℝ)
    (hweighted : ∀ (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
      (∀ x,‖B x‖≤L) → |signedTrace volume (fun x => B x*F x)|≤L*E)
    (S : Set ℍ) (hS : MeasurableSet S) (w : ℂ) :
    let k := metricCapCoefficient M δ ν J
    let B := (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*M.lower⁻¹
    |∫ x in S,(k x*conj (k x)*matrix (F x) 1 1*w).re|≤B^2*‖w‖*E := by
  intro k B
  have hk : Measurable k := metricCapCoefficient_measurable M δ ν J
  have hb (x : ℍ) : ‖k x*conj (k x)*w‖≤B^2*‖w‖ := by
    rw [norm_mul,norm_mul,Complex.norm_conj,←pow_two]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (metricCapCoefficient_bound M δ ν J x) 2) (norm_nonneg w)
  have hh := RawCommonReconstruction.local_weighted_trace_bound F E hweighted S hS
    (fun x => k x*conj (k x)*w)
    ((hk.mul (Complex.continuous_conj.measurable.comp hk)).mul measurable_const)
    (B^2*‖w‖) (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hb
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

#print axioms metric_cap_local_regular_error

#print axioms metricCapCoefficient_measurable
#print axioms metricCapCoefficient_bound
#print axioms metricCappedExpression_regular_diagonal
end QuantitativeMaass
