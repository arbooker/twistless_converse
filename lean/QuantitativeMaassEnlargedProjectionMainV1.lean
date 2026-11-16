module

public import QuantitativeMaassEnlargedCountingMainV1
public import QuantitativeMaassMovingProjectionMainV1
public import QuantitativeMaassEnlargedWindowBoundsV1
public import QuantitativeMaassCountingRootApproximationV1
public import QuantitativeArithmeticMaassSourceColumnEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticSectorSigns AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticRegularTrace QuantitativeNewGap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Replace the finite Gram coefficient by the true counting-sector
coefficient in the moving regular main term. The cutoff mass is unchanged. -/
theorem enlarged_projection_main_decay (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (e : Sector N)
    (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t =>
      let mass := ∫ x in cutoffRectangle (movingLowerEdge δ P ε t) t,
        ‖upperFunction (cutoffSeed (movingLowerEdge δ P ε t) D t
          (movingLowerEdge_pos hδ P ε t)).toFun x‖^2
      let b := (countingSectorSpace N hN e).starProjection
        (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)
      Real.exp (W*Strong.strongScale t)*
        ‖enlargedMovingExpressionMain N (ambientSectorGramExpression N hN e) δ P D hδ K hc ε t-
          mass*(b*windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re‖/
        (t*ε t)) atTop (𝓝 0) := by
  let Q := (countingSectorSpace N hN e).starProjection
  let F := fun m => Counting.sectorNewFilter N hN e m
  let A := fun m => (F m).adjoint.comp (F m)
  let b := Q (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)
  let mass := fun t => ∫ x in cutoffRectangle (movingLowerEdge δ P ε t) t,
    ‖upperFunction (cutoffSeed (movingLowerEdge δ P ε t) D t
      (movingLowerEdge_pos hδ P ε t)).toFun x‖^2
  obtain ⟨C,hC,hwin⟩ := enlargedWindowIdentity_bound K he hc hK hm
  have hl := (Counting.sectorGram_weighted_limit N hN hAd e ε
    (hε.mono (fun _ h => h.1)) hp (W+4)).const_mul C
  rw [mul_zero] at hl
  apply squeeze_zero' _ _ hl
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_ge_atTop (3:ℝ),radius_resolves_window ε hε hp,
      movingCutoffMass_bound δ P D hδ hP ε hε hp,
      QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp]
      with t heps ht hresolve hmass hparam
    have ht0 : 0<t := by linarith
    let w := windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))
    let a := A (growingLVDegree t) (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)
    have hw : ‖w‖≤C*t*ε t := hwin _ t (ε t) _ _ (le_max_left _ _) (by linarith) heps.1.le heps.2 hresolve.2
      hparam.2.2 (by linarith [hparam.1,heps.1])
      (by linarith [hparam.2.1,heps.2]) (by linarith [hparam.2.1])
    have hab : ‖a-b‖≤‖A (growingLVDegree t)-Q‖ := Counting.root_coefficient_difference N _ _
    rw [enlargedMovingExpressionMain_counting N _ A (Counting.ambientSectorGramExpression_realizes N hN e)]
    change Real.exp (W*Strong.strongScale t)*
      ‖mass t*(a*w).re-mass t*(b*w).re‖/(t*ε t)≤_
    have heq : mass t*(a*w).re-mass t*(b*w).re=mass t*((a-b)*w).re := by
      rw [sub_mul,Complex.sub_re]
      ring
    have hdiff : ‖mass t*(a*w).re-mass t*(b*w).re‖≤
        Real.exp (4*Strong.strongScale t)*‖A (growingLVDegree t)-Q‖*(C*t*ε t) := by
      rw [heq,norm_mul]
      have hre : ‖((a-b)*w).re‖≤‖(a-b)*w‖ := by
        simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm ((a-b)*w)
      calc
        _ ≤ ‖mass t‖*(‖a-b‖*‖w‖) := mul_le_mul_of_nonneg_left
          (hre.trans_eq (norm_mul _ _)) (norm_nonneg _)
        _ ≤ Real.exp (4*Strong.strongScale t)*(‖A (growingLVDegree t)-Q‖*(C*t*ε t)) :=
          mul_le_mul hmass (mul_le_mul hab hw (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
        _ = _ := by ring
    calc
      _ ≤ Real.exp (W*Strong.strongScale t)*
          (Real.exp (4*Strong.strongScale t)*‖A (growingLVDegree t)-Q‖*(C*t*ε t))/(t*ε t) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le)
          (mul_pos ht0 heps.1).le
      _ = C*(Real.exp ((W+4)*Strong.strongScale t)*‖A (growingLVDegree t)-Q‖) := by
        rw [add_mul,Real.exp_add]
        field_simp [ht0.ne',heps.1.ne']
      _ ≤ C*(Real.exp ((W+4)*Strong.strongScale t)*‖A (growingLVDegree t)-Q‖/ε t) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply (le_div_iff₀ heps.1).mpr
        exact mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) heps.2

#print axioms enlarged_projection_main_decay
end QuantitativeMaass.Scheduled
