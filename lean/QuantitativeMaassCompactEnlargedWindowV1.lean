module

public import QuantitativeMaassCompactExpressionKernelTraceV1
public import QuantitativeMaassExpressionRegularIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticRegularTrace
open QuantitativeHolomorphic
open scoped SchwartzMap FourierTransform
namespace QuantitativeMaass

/-- The actual compact-input window-column trace, with no replacement
packet, is compared to its regular integral. The constants are uniform
before choosing the finite expression and compact rectangle. -/
theorem compact_enlarged_window_regular_comparison (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ {ι : Type*} [Countable ι]
      (_basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
      (a b : ℝ) (ha : 0<a) (E : Expression) (B : ℝ),0≤B →
      let S := upperRectangle 0 1 a b
      let hS := upperRectangle_compact 0 1 a b ha
      let F := compactInputExpression S hS.measurableSet E
      ExpressionMatrixBound F B → ∀ (L R ε t h : ℝ) (hR : 1≤R),
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
      |columnLinearTrace (quotientMeasure 0)
        (fun z => P (cylinderTimeColumn f hfc hfe (V*R) (mul_nonneg hV.le hRp.le) hs z))
        (Z.adjoint.comp ((holomorphicSum E 0).comp Z))-
        (∫ x in S,(matrix (regularSum F x) 1 1*
          windowIdentityContribution K hc R hRp (t-h) (t+ε+h)).re)|≤
      expressionBound F*(1+4*B)^40*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := concrete_expression_kernel_regular_comparison K he hc o
  refine ⟨U,2*C,hU,mul_pos (by norm_num) hC,?_⟩
  intro ι _ basis a b ha E B hB S hS F hF L R ε t h hR hL hε hε1 ht hh0 hhε hSB
    hRp f hfc hfe V hV hs P Z
  have hstrip : ∀ᵐ z ∂volume.restrict S,z∈strip := by
    have hle : volume.restrict S≤quotientMeasure 0 := by
      rw [←cylinder_rectangle_measure a b ha]
      exact Measure.restrict_le_self
    apply (ae_mono hle)
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  have hreal : ∀ s,star (f s)=f s := symmetricWindowTimeTest_real K he R (t-h) (t+ε+h)
  rw [compact_input_expression_kernel_trace basis f hfc hfe hreal (V*R)
    (mul_nonneg hV.le hRp.le) hs ha b E]
  have hh := hbound F B hB hF S hS L R (ε/2+h) (t+ε/2) hR hL
    (by positivity) (by linarith) (by linarith) hSB hstrip
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

#print axioms compact_enlarged_window_regular_comparison
end QuantitativeMaass
