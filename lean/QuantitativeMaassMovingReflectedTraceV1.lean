module

public import QuantitativeMaassCrossReflectedWindowV1
public import QuantitativeMaassCrossLocalizedGrowthV1
public import QuantitativeMaassCrossTraceScheduleV1
public import QuantitativeMaassMovingBroadDeficitV1
public import QuantitativeMaassCutoffStripSupportV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport QuantitativeHolomorphic
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The actual reflected moving-cutoff trace is negligible on the
one-sided window schedule. The finite expression may grow with the chosen
degree; its overlap and matrix costs have been proved uniformly. -/
theorem moving_expression_reflected_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) (E : ℕ → Expression)
    (A : ℕ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hE : ExponentialExpressionGrowth E) (hA : ∀ m, QuotientRealizes N (E m) (A m))
    (δ P D : ℝ) (hδ : 0 < δ) (hP : 0 ≤ P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      columnLinearTrace (quotientMeasure 0)
        (fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t)
          (cylinderAutomorphic (column K hc he ε t z)))
        ((reflectionIsometry N).toContinuousLinearMap.comp (A (growingLVDegree t)))/(t*ε t))
      atTop (𝓝 0) := by
  let a := fun t => movingLowerEdge δ P ε t
  let S := fun t => cutoffRectangle (a t) t
  let hS : ∀ t, IsCompact (S t) := fun t =>
    upperRectangle_compact 0 1 (a t) _ (movingLowerEdge_pos hδ P ε t)
  let u := fun t => cutoffSeed (a t) D t (movingLowerEdge_pos hδ P ε t)
  let v := fun t => upperFunction (u t).toFun
  have hv (t : ℝ) : Measurable (v t) := (upperFunction_continuous (u t).smooth).measurable
  have hvb (t : ℝ) (z : ℍ) : ‖v t z‖ ≤ 1 :=
    cutoffSeed_bound (a t) D t (movingLowerEdge_pos hδ P ε t) z
  let F := fun t => compactInputExpression (S t) (hS t).measurableSet
    (reflectedLocalExpression N (S t) (S t) (hS t) (hS t) (v t) (v t) (hv t) (hv t)
      1 1 zero_le_one zero_le_one (hvb t) (hvb t) (E (growingLVDegree t)))
  have hball := movingCutoffRectangle_ball hδ P hP ε hε hp
  obtain ⟨G,H,hG,hH,hcost⟩ := CrossCompactBranch.scheduled_localExpression_growth N E hE
    (fun t => (fun z : ℍ => J • z) '' S t) S
    (fun t => (hS t).image (continuous_const_smul J)) hS
    (fun t z => v t (J • z)) v
    (fun t => (hv t).comp (continuous_const_smul J).measurable) hv
    (fun t z => hvb t (J • z)) hvb
    (hball.mono (fun t ht => ⟨CrossCompactBranch.reflected_ball_I (S t) _ ht,ht⟩))
  let B := fun t => Real.exp (G*(growingLVDegree t:ℝ)+H*Strong.strongScale t)
  change ∀ᶠ t in atTop, expressionBound (F t) ≤ B t ∧ ExpressionMatrixBound (F t) (B t) at hcost
  have hH0 : 0 ≤ H := (by norm_num : (0:ℝ) ≤ 4).trans hH
  have hgeometry : ∀ᶠ t in atTop,
      radius ε t ≤ H*Strong.strongScale t ∧ 4*Strong.strongScale t ≤ H*Strong.strongScale t := by
    filter_upwards [radius_mul_le_half_strong 1 zero_le_one ε hε hp] with t ht
    have hs : 0 ≤ Strong.strongScale t := sq_nonneg _
    constructor
    · simp only [one_mul] at ht
      nlinarith [mul_le_mul_of_nonneg_right hH hs]
    · exact mul_le_mul_of_nonneg_right hH hs
  obtain ⟨U,C,hU,hC,hbound⟩ := cross_window_reflected_trace_bound K he hc I
  have hlim := Strong.finite_expression_geometric_cost_limit ε hε hp F B
    (radius ε) (fun t => 4*Strong.strongScale t) G H U C W hG hH0 hU.le hC.le
    (hcost.mono (fun t ht => ⟨ht.1,(Real.exp_pos _).le,le_rfl⟩)) hgeometry
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hε,hcost,hball,eventually_ge_atTop (1:ℝ)] with t heps htCost htBall ht
  have hsupp := cutoffSeed_support (a t) D t (movingLowerEdge_pos hδ P ε t)
  have hstrip : Function.support (v t) ⊆ strip :=
    rectangleSmoothSeed_support_strip (a t) _ _ (movingLowerEdge_pos hδ P ε t) (Real.exp_pos _)
  have hb := hbound basis N (a t) (Real.exp (Strong.strongScale t/2))
    (movingLowerEdge_pos hδ P ε t) (u t) hsupp hstrip 1 zero_le_one
    (fun z _ => hvb t z) (E (growingLVDegree t)) (A (growingLVDegree t)) (hA _)
    (B t) (Real.exp_pos _).le htCost.2 (4*Strong.strongScale t) (radius ε t) (ε t) t
    (le_max_left _ _) (mul_nonneg (by norm_num) (sq_nonneg _)) heps.1.le heps.2 ht htBall
  change |columnLinearTrace (quotientMeasure 0)
    (fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t)
      (cylinderAutomorphic (column K hc he ε t z)))
    ((reflectionIsometry N).toContinuousLinearMap.comp (A (growingLVDegree t)))| ≤
      expressionBound (F t)*(1+4*B t)^40*C*Real.sqrt t*(ε t)^2*
        Real.exp (U*radius ε t+30*(4*Strong.strongScale t)) at hb
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),
    abs_of_pos (mul_pos ht0 heps.1)]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) (mul_pos ht0 heps.1).le).trans_eq
  ring

#print axioms moving_expression_reflected_trace_decay

end QuantitativeMaass.Scheduled
