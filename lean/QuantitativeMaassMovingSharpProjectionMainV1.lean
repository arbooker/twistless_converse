module

public import QuantitativeMaassMovingCutoffMassV1
public import QuantitativeMaassMovingSectorProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticRegularTrace QuantitativeNewGap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The regular counting-sector main term with the literal sharp rectangle. -/
def movingSharpSectorProjectionMain (N : ℕ) (hN : 0<N) (e : Sector N)
    (δ C : ℝ) (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  volume.real (cutoffRectangle (movingLowerEdge δ C ε t) t)*
    ((countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)*
      windowIdentityContribution K hc (radius ε t) (radius_pos ε t) t (t+ε t)).re

/-- Smoothing changes the exact regular main term negligibly, including
its spatial mass, on the original shrinking-window scale. -/
theorem moving_sharp_projection_main_decay (N : ℕ) (hN : 0<N) (e : Sector N)
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖movingSharpSectorProjectionMain N hN e δ C K hc ε t-
        movingSectorProjectionMain N hN e δ C D hδ K hc ε t‖/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hwin⟩ := windowIdentityContribution_resolved_bound K he hc hK hm
  have hlim := (movingCutoffMass_difference_limit hδ C hC ε hε hp D W hD hDW).const_mul B
  rw [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ),radius_resolves_window ε hε hp] with t heps ht hresolve
    have ht0 : 0<t := zero_lt_one.trans_le ht
    let b := (countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)
    let w := windowIdentityContribution K hc (radius ε t) (radius_pos ε t) t (t+ε t)
    let a := volume.real (cutoffRectangle (movingLowerEdge δ C ε t) t)
    let m := ∫ z in cutoffRectangle (movingLowerEdge δ C ε t) t,
      ‖upperFunction (cutoffSeed (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)).toFun z‖^2
    have hw : ‖w‖≤B*t*ε t := hwin _ _ _ (le_max_left _ _) ht heps.1.le heps.2 hresolve.2
    have hb : ‖b‖≤1 := Counting.sector_projection_root_norm N hN e
    have hre : ‖(b*w).re‖≤B*t*ε t := by
      calc
        _ ≤ ‖b*w‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (b*w)
        _ = ‖b‖*‖w‖ := norm_mul _ _
        _ ≤ 1*(B*t*ε t) := mul_le_mul hb hw (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    change Real.exp (W*Strong.strongScale t)*‖a*(b*w).re-m*(b*w).re‖/(t*ε t)≤
      B*(Real.exp (W*Strong.strongScale t)*‖a-m‖)
    rw [←sub_mul,norm_mul]
    calc
      _ ≤ Real.exp (W*Strong.strongScale t)*(‖a-m‖*(B*t*ε t))/(t*ε t) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hre (norm_nonneg _)) (Real.exp_pos _).le) (mul_pos ht0 heps.1).le
      _ = _ := by field_simp [ht0.ne',heps.1.ne']

#print axioms moving_sharp_projection_main_decay
end QuantitativeMaass.Scheduled
