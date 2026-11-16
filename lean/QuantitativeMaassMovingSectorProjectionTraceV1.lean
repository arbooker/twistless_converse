module

public import QuantitativeMaassMovingSectorParityTraceV1
public import QuantitativeMaassMovingProjectionMainV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticRegularTrace QuantitativeNewGap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The true counting-sector coefficient with the actual spatial mass
and the one-sided spherical window contribution. -/
def movingSectorProjectionMain (N : ℕ) (hN : 0<N) (e : Sector N)
    (δ P D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  (∫ x in cutoffRectangle (movingLowerEdge δ P ε t) t,
    ‖upperFunction (cutoffSeed (movingLowerEdge δ P ε t) D t
      (movingLowerEdge_pos hδ P ε t)).toFun x‖^2)*
    ((countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)*
      windowIdentityContribution K hc (radius ε t) (radius_pos ε t) t (t+ε t)).re

/-- Actual filtered parity trace compared with the true counting-sector
projection coefficient. This retains the spatial mass; identifying the
canonical counting normalization is a separate step. -/
theorem moving_sector_projection_trace_decay {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N : ℕ) [NeZero N] (hN : 0<N) (hAd : GridAdmissibleGap.Admissible N)
    (e : Sector N) (σ : ℝ)
    (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let c := fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t
        (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))
      let F := ambientSectorNewFilter N hN e (growingLVDegree t)
      Real.exp (W*Strong.strongScale t)*
        (columnLinearTrace (quotientMeasure 0) (fun z => F (c z)) (parityProjection N σ)-
          movingSectorProjectionMain N hN e δ P D hδ K hc ε t/2)/(t*ε t))
      atTop (𝓝 0) := by
  have ht := moving_sector_parity_trace_decay basis N hN e σ δ P D hδ hP K hc he ε hε hp W
  have hn := moving_projection_main_decay N hN hAd e δ P D hδ hP K hc he hK hm ε hε hp W
  change Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
    ‖movingExpressionMain N (ambientSectorGramExpression N hN e) δ P D hδ K hc ε t-
      movingSectorProjectionMain N hN e δ P D hδ K hc ε t‖/(t*ε t)) atTop (𝓝 0) at hn
  have hr : Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (movingExpressionMain N (ambientSectorGramExpression N hN e) δ P D hδ K hc ε t-
        movingSectorProjectionMain N hN e δ P D hδ K hc ε t)/(t*ε t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hn
    filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht0
    simp only [norm_div,norm_mul,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),abs_of_pos ht0,abs_of_pos heps.1,le_refl]
  have hh := ht.add (hr.div_const 2)
  simp only [zero_div,add_zero] at hh
  convert hh using 1
  funext t
  dsimp only
  ring

#print axioms moving_sector_projection_trace_decay
end QuantitativeMaass.Scheduled
