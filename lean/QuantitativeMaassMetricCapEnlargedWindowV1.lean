module

public import QuantitativeMaassCompactEnlargedWindowV1
public import QuantitativeMaassMetricCapExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

/-- Quantitative geometric comparison for the actual finite expression
containing both inverse metric and inverse cap. All matrix and coefficient
costs are expressed in terms of the original filter. -/
theorem metric_cap_enlarged_window_regular_comparison (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ {N : ℕ} (M : ScalarCylinderMetric N)
      (δ : ℝ) (m J : ℕ) {ι : Type*} [Countable ι]
      (_basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
      (a b : ℝ) (ha : 0<a) (E : Expression) (B : ℝ),0≤B → ExpressionMatrixBound E B →
      let S := upperRectangle 0 1 a b
      let hS := upperRectangle_compact 0 1 a b ha
      let F := compactInputExpression S hS.measurableSet (metricCappedExpression M δ m J E)
      ∀ (L R ε t h : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t → 0≤h → 2*h≤ε → S⊆Metric.closedBall o L →
      let hRp := lt_of_lt_of_le zero_lt_one hR
      let f := windowTimeSchwartz K hc R hRp (t-h) (t+ε+h)
      let hfc := symmetricWindowTimeTest_compact K hc R (t-h) (t+ε+h) hRp
      let hfe := symmetricWindowTimeTest_even K he R (t-h) (t+ε+h)
      let V := (symmetricWindowTimeTest_uniform_support K hc).choose
      let hV := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1
      let hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hRp (t-h) (t+ε+h)
      let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
      let Z := cylinderZeroExtension.toContinuousLinearMap
      let D := (terminalInverseWeightBand δ m J).comp M.change.symm.toContinuousLinearMap
      |columnLinearTrace (quotientMeasure 0)
        (fun z => P (cylinderTimeColumn f hfc hfe (V*R) (mul_nonneg hV.le hRp.le) hs z))
        (D.comp ((Z.adjoint.comp ((holomorphicSum E 0).comp Z)).comp D.adjoint))-
        (∫ x in S,(matrix (regularSum F x) 1 1*
          windowIdentityContribution K hc R hRp (t-h) (t+ε+h)).re)|≤
      ((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*(M.lower⁻¹)^2*expressionBound E)*
        (1+128*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := compact_enlarged_window_regular_comparison K he hc o
  refine ⟨U,C,hU,hC,?_⟩
  intro N M δ m J ι _ basis a b ha E B hB hE S hS F L R ε t h hR hL hε hε1 ht hh0 hhε hSB
    hRp f hfc hfe V hV hs P Z D
  have hcorner := expressionMatrixBound_singleton_one (corner S hS.measurableSet) rfl
  have hmatrix : ExpressionMatrixBound F (32*B) := by
    have hh := (metricCappedExpression_matrix M δ m J E hB hE).compose hcorner zero_le_one
    convert hh using 1
    · rfl
    · ring
  have hmass : expressionBound F≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2*(M.lower⁻¹)^2*expressionBound E := by
    have hh := metricCappedExpression_mass M δ m J E
    change expressionBound (compactInputExpression S hS.measurableSet (metricCappedExpression M δ m J E))≤_
    rw [compactInputExpression,expressionBound_compose]
    have hone : expressionBound [corner S hS.measurableSet]=1 := by
      simp only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rfl
    rw [hone,mul_one]
    exact hh
  have hh := hbound basis a b ha (metricCappedExpression M δ m J E) (32*B)
    (by positivity) hmatrix L R ε t h hR hL hε hε1 ht hh0 hhε hSB
  dsimp only at hh
  rw [metricCappedExpression_cylinder] at hh
  have hscale : 1+4*(32*B)=1+128*B := by ring
  rw [hscale] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ hC.le
  exact mul_le_mul_of_nonneg_right hmass (by positivity)

#print axioms metric_cap_enlarged_window_regular_comparison
end QuantitativeMaass
