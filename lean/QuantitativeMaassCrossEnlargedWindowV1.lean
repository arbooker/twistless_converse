module

public import QuantitativeMaassCrossExpressionKernelV1
public import QuantitativeMaassExpressionRegularIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual compact-transfer window trace has a uniform geometric
comparison with the regular diagonal of its full localized expression.
Matrix height and coefficient mass include the intermediate congruence sum. -/
theorem cross_enlarged_window_regular_comparison (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ, 0 < U ∧ 0 < C ∧ ∀ {ι : Type*} [Countable ι]
      (_basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
      (N : ℕ) (a b : ℝ) (ha : 0 < a) (u : SmoothUpperSeed)
      (hu : tsupport (upperFunction u.toFun) ⊆ upperRectangle 0 1 a b)
      (_hstrip : Function.support (upperFunction u.toFun) ⊆ strip)
      (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
      (hbound : ∀ z ∈ upperRectangle 0 1 a b, ‖upperFunction u.toFun z‖ ≤ B₀)
      (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N),
      QuotientRealizes N E A →
      let S := upperRectangle 0 1 a b
      let hS := upperRectangle_compact 0 1 a b ha
      let v := upperFunction u.toFun
      let hv := (upperFunction_continuous u.smooth).measurable
      let hb := CrossCompactBranch.cutoff_global_bound v S hu B₀ hB₀ hbound
      let E' := CrossCompactBranch.localExpression N S S hS hS v v hv hv B₀ B₀ hB₀ hB₀ hb hb E
      let F := compactInputExpression S hS.measurableSet E'
      let T := crossQuotientLocalization N 0 S hS u hbound
      ∀ (B : ℝ), 0 ≤ B → ExpressionMatrixBound F B →
      ∀ (L R ε t h : ℝ) (hR : 1 ≤ R),
      0 ≤ L → 0 ≤ ε → ε ≤ 1 → 1 ≤ t → 0≤h → 2*h≤ε → S ⊆ Metric.closedBall o L →
      let hRp := lt_of_lt_of_le zero_lt_one hR
      let f := windowTimeSchwartz K hc R hRp (t-h) (t+ε+h)
      let hfc := symmetricWindowTimeTest_compact K hc R (t-h) (t+ε+h) hRp
      let hfe := symmetricWindowTimeTest_even K he R (t-h) (t+ε+h)
      let V := (symmetricWindowTimeTest_uniform_support K hc).choose
      let hV := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1
      let hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hRp (t-h) (t+ε+h)
      |columnLinearTrace (quotientMeasure 0)
        (fun z => T (cylinderAutomorphic
          (cylinderTimeColumn f hfc hfe (V*R) (mul_nonneg hV.le hRp.le) hs z))) A -
        (∫ x in S, (matrix (regularSum F x) 1 1*
          windowIdentityContribution K hc R hRp (t-h) (t+ε+h)).re)| ≤
      expressionBound F*(1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := concrete_expression_kernel_regular_comparison K he hc o
  refine ⟨U,2*C,hU,mul_pos (by norm_num) hC,?_⟩
  intro ι _ basis N a b ha u hu hstrip B₀ hB₀ hbu E A hA S hS v hv hb E' F T
    B hB hF L R ε t h hR hL hε hε1 ht hh0 hhε hSB hRp f hfc hfe V hV hs
  have hreal : ∀ s, star (f s)=f s := symmetricWindowTimeTest_real K he R (t-h) (t+ε+h)
  rw [crossQuotientLocalization_expression_kernel_trace basis f hfc hfe hreal (V*R)
    (mul_nonneg hV.le hRp.le) hs N a b ha u hu hstrip B₀ hB₀ hbu E A hA]
  have hh := hbound F B hB hF S hS L R (ε/2+h) (t+ε/2) hR hL
    (by positivity) (by linarith) (by linarith) hSB (upperRectangle_ae_strip a b ha)
  simp only [windowSquareProfile,show t+ε/2-(ε/2+h)=t-h by ring,
    show t+ε/2+(ε/2+h)=t+ε+h by ring] at hh
  have hsqrt : Real.sqrt (t+ε/2) ≤ 2*Real.sqrt t := by
    calc
      _ ≤ Real.sqrt (4*t) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have heps : (ε/2+h)^2 ≤ ε^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hmass := expressionBound_nonneg F
  apply hh.trans
  calc
    _ ≤ expressionBound F*(1+4*B)^40*C*(2*Real.sqrt t)*ε^2*Real.exp (U*R+30*L) := by
      gcongr
    _ = _ := by ring

#print axioms cross_enlarged_window_regular_comparison

end QuantitativeMaass
