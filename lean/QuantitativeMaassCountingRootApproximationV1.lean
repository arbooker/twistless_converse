module

public import QuantitativeMaassCountingSectorApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter ContinuousLinearMap AsymptoticSectorSigns AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticRegularTrace QuantitativeNewGap
open scoped Topology lp
namespace QuantitativeMaass.Counting

attribute [local instance] Classical.propDecidable

/-- Evaluation at the root is continuous in operator norm on the actual
counting quotient, with constant one. -/
theorem root_coefficient_difference (N : ℕ) (A B : Space N→L[ℂ]Space N) :
    ‖A (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)-
      B (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)‖≤‖A-B‖ := by
  have hd : ‖delta (classOf (gamma N) 1)‖=1 := by
    classical
    simp [AsymptoticRegularTrace.delta,lp.norm_single]
  change ‖((A-B) (delta (classOf (gamma N) 1))) (classOf (gamma N) 1)‖≤_
  exact (lp.norm_apply_le_norm (by norm_num) _ _).trans
    (by simpa only [hd,mul_one] using (A-B).le_opNorm (delta (classOf (gamma N) 1)))

theorem sector_projection_root_nonneg (N : ℕ) (hN : 0<N) (e : Sector N) :
    0≤((countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)).re := by
  let P := (countingSectorSpace N hN e).starProjection
  have hP : P.adjoint.comp P=P := by
    rw [(isSelfAdjoint_starProjection _).adjoint_eq]
    exact Submodule.isIdempotentElem_starProjection _
  change 0≤(matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)).re
  rw [←hP,matrix_gram]
  positivity

theorem sector_projection_root_norm (N : ℕ) (hN : 0<N) (e : Sector N) :
    ‖(countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)‖≤1 := by
  have h : ‖(countingSectorSpace N hN e).starProjection
      (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)‖≤
      ‖(countingSectorSpace N hN e).starProjection‖ := by
    simpa using root_coefficient_difference N (countingSectorSpace N hN e).starProjection 0
  exact h.trans (Submodule.starProjection_norm_le _)

/-- The regular coefficient of the same finite Gram expression converges
to that of the true counting-sector projection, with the required weight. -/
theorem sectorGram_root_weighted_limit (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (e : Sector N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ)
    (x : UpperHalfPlane) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖((ambientSectorGramExpression N hN e (growingLVDegree t)).map
          (fun b => if b.label∈gamma N then b.coefficient x else 0)).sum-
        (countingSectorSpace N hN e).starProjection
          (delta (classOf (gamma N) 1)) (classOf (gamma N) 1)‖/ε t)
      atTop (𝓝 0) := by
  apply squeeze_zero' (hε.mono (fun t ht => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ht.le)) _
    (sectorGram_weighted_limit N hN hAd e ε hε hp W)
  filter_upwards [hε] with t ht
  apply div_le_div_of_nonneg_right _ ht.le
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [←ambientSectorGramExpression_root]
  exact root_coefficient_difference N _ _

#print axioms root_coefficient_difference
#print axioms sector_projection_root_nonneg
#print axioms sector_projection_root_norm
#print axioms sectorGram_root_weighted_limit
end QuantitativeMaass.Counting
