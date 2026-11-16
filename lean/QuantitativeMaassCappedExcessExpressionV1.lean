module

public import QuantitativeMaassInverseWeightExpressionV1
public import QuantitativeMaassFullColumnExpressionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson QuantitativeHolomorphic
open scoped SchwartzMap
namespace QuantitativeMaass

/-- The bounded inverse cap conjugates the same finite expression in both
representations. Its branches introduce no new rational transformations. -/
def cappedSandwichExpression (ε : ℝ) (m J : ℕ) (E : Expression) : Expression :=
  composeExpression (terminalInverseWeightExpression ε m J)
    (composeExpression E (adjointExpression (terminalInverseWeightExpression ε m J)))

theorem cappedSandwichExpression_physical (ε : ℝ) (m J : ℕ) (E : Expression) :
    holomorphicSum (cappedSandwichExpression ε m J E) 0=
      (holomorphicSum (terminalInverseWeightExpression ε m J) 0).comp
        ((holomorphicSum E 0).comp
          (holomorphicSum (terminalInverseWeightExpression ε m J) 0).adjoint) := by
  simp only [cappedSandwichExpression,holomorphicSum_compose,holomorphicSum_adjoint]

theorem cappedSandwichExpression_regular (ε : ℝ) (m J : ℕ) (E : Expression) (z : ℍ) :
    regularSum (cappedSandwichExpression ε m J E) z=
      (regularSum (terminalInverseWeightExpression ε m J) z).comp
        ((regularSum E z).comp
          (regularSum (terminalInverseWeightExpression ε m J) z).adjoint) := by
  simp only [cappedSandwichExpression,regularSum_compose,regularSum_adjoint]

theorem cappedSandwichExpression_matrix (ε : ℝ) (m J : ℕ) (E : Expression)
    {B : ℝ} (hB : 0≤B) (hE : ExpressionMatrixBound E B) :
    ExpressionMatrixBound (cappedSandwichExpression ε m J E) (4*B) := by
  have hK := terminalInverseWeightExpression_matrix ε m J
  have hh := hK.compose (hE.compose hK.adjoint zero_le_one) (by positivity : 0≤2*B*1)
  convert hh using 1
  · rfl
  · ring

theorem cappedSandwichExpression_mass (ε : ℝ) (m J : ℕ) (E : Expression) :
    expressionBound (cappedSandwichExpression ε m J E)≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*expressionBound E := by
  rw [cappedSandwichExpression,expressionBound_compose,expressionBound_compose,
    expressionBound_adjoint]
  have h := terminalInverseWeightExpression_mass ε m J
  have h0 := expressionBound_nonneg (terminalInverseWeightExpression ε m J)
  have hE := expressionBound_nonneg E
  calc
    _ = expressionBound (terminalInverseWeightExpression ε m J)^2*expressionBound E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h 2) hE

private theorem sandwich_transport {H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (S : H→L[ℂ]V) (B : V→L[ℂ]V) (K T : H→L[ℂ]H) (h : B.comp S=S.comp K) :
    B.comp ((S.comp (T.comp S.adjoint)).comp B.adjoint)=
      S.comp ((K.comp (T.comp K.adjoint)).comp S.adjoint) := by
  have ha := congrArg (fun F : H→L[ℂ]V => F.adjoint) h
  simp only [adjoint_comp] at ha
  calc
    _ = (B.comp S).comp (T.comp (S.adjoint.comp B.adjoint)) := by simp only [comp_assoc]
    _ = (S.comp K).comp (T.comp (K.adjoint.comp S.adjoint)) := by rw [h,ha]
    _ = _ := by simp only [comp_assoc]

/-- The original centered capped trace is exactly the physical trace of the
unweighted centered columns with the bounded inverse cap conjugated onto the
operator. Neither the center projection nor the canonical subtraction is dropped. -/
theorem centeredCapped_physical_trace_unweight
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) (m : ℕ)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    let B := holomorphicSum (terminalInverseWeightExpression ε m ⌈(m:ℝ)*R+1⌉₊) 0
    let S := cylinderZeroExtension.toContinuousLinearMap
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip ε))
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T=
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip ε))
      (fun z => cylinderZeroExtension (cylinderCenteredTimeColumn f hc he R hR hs z))
      (B.comp ((S.comp (T.comp S.adjoint)).comp B.adjoint)) := by
  intro B S
  rw [centeredCapped_column_trace_unweight f hc he R hR hs hε m T]
  rw [sandwich_transport S B _ T (terminalInverseWeightExpression_intertwines ε m _)]
  exact (columnLinearTrace_isometry _ _ cylinderZeroExtension _).symm

/-- Conjugating an explicit operator approximation costs only the square of
the proved coefficient mass. -/
theorem cappedSandwichExpression_error (ε : ℝ) (m J : ℕ) (E : Expression)
    (T : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space)
    {δ : ℝ} (hδ : ‖holomorphicSum E 0-T‖≤δ) :
    let B := holomorphicSum (terminalInverseWeightExpression ε m J) 0
    ‖holomorphicSum (cappedSandwichExpression ε m J E) 0-B.comp (T.comp B.adjoint)‖≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*δ := by
  intro B
  have hB := (holomorphicSum_norm_le (terminalInverseWeightExpression ε m J) 0).trans
    (terminalInverseWeightExpression_mass ε m J)
  have hd : 0≤δ := (norm_nonneg _).trans hδ
  rw [cappedSandwichExpression_physical]
  change ‖B.comp ((holomorphicSum E 0).comp B.adjoint)-B.comp (T.comp B.adjoint)‖≤_
  rw [←comp_sub,←sub_comp]
  calc
    _ ≤ ‖B‖*(‖holomorphicSum E 0-T‖*‖B.adjoint‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg B))
    _ = ‖B‖^2*‖holomorphicSum E 0-T‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
    _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (norm_nonneg B) hB 2) hδ (norm_nonneg _) (sq_nonneg _)

#print axioms cappedSandwichExpression_physical
#print axioms cappedSandwichExpression_regular
#print axioms cappedSandwichExpression_matrix
#print axioms cappedSandwichExpression_mass
#print axioms centeredCapped_physical_trace_unweight
#print axioms cappedSandwichExpression_error
end QuantitativeMaass
