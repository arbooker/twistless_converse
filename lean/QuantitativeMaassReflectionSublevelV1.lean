module

public import QuantitativeMaassReflectionDisplacementV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousConstSMul (gamma N) ℍ :=
  ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩

/-- Reflection preserves the Euclidean norm, so the original denominator
bound also controls every reflected branch on the same centre ball. -/
theorem diagonalOrbitSet_reflected_denominator_bound (N : ℕ) (o z : ℍ) (L D : ℝ)
    (hz : dist z o≤L) (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) :
    ‖((representative γ) 1 0:ℂ)*((J•z:ℍ):ℂ)+(representative γ) 1 1‖≤
      displacementDenominatorBound o L D := by
  have hc := diagonalOrbitSet_entry_bound N o D γ hγ 1 0
  have hd := diagonalOrbitSet_entry_bound N o D γ hγ 1 1
  have hcast (a : ℤ) : ‖(a:ℂ)‖=|(a:ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖((representative γ) 1 0:ℂ)*((J•z:ℍ):ℂ)‖+‖((representative γ) 1 1:ℂ)‖ := norm_add_le _ _
    _ = |((representative γ) 1 0:ℝ)| * ‖(z:ℂ)‖+|((representative γ) 1 1:ℝ)| := by
      rw [norm_mul,hcast,hcast,coe_J_smul,norm_neg,Complex.norm_conj]
    _ ≤ Real.exp (D/2+dist o I)*(‖(o:ℂ)‖+o.im*Real.exp L)+Real.exp (D/2+dist o I) := by
      apply add_le_add _ hd
      exact mul_le_mul hc (norm_coe_le_on_ball o z L hz) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by unfold displacementDenominatorBound; ring

/-- Explicit area constant for reflected hyperbolic near returns. -/
def reflectedSublevelConstant (o : ℍ) (L D : ℝ) : ℝ :=
  (1/(o.im/Real.exp L))^2*
    (4*(‖(o:ℂ)‖+o.im*Real.exp L)/(o.im/Real.exp L)+
      8*(‖(o:ℂ)‖+o.im*Real.exp L))*
    displacementDenominatorBound o L D*localDisplacementScale o L+
  volume.real (Metric.closedBall o L)

theorem reflectedSublevelConstant_nonneg (o : ℍ) (L D : ℝ) :
    0≤reflectedSublevelConstant o L D := by
  have hH := localDisplacementScale_pos o L
  have hD := displacementDenominatorBound_pos o L D
  have hi := o.im_pos
  unfold reflectedSublevelConstant
  positivity

/-- Uniform linear sublevel area for every reflected congruence branch,
including the identity representative, for all positive radii. -/
theorem diagonalOrbitSet_reflected_hyperbolic_sublevel (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (γ•(J•z)) z<r}≤
      ENNReal.ofReal (reflectedSublevelConstant o L D*r) := by
  let H := localDisplacementScale o L
  let B := displacementDenominatorBound o L D
  let V := volume.real (Metric.closedBall o L)
  let X := ‖(o:ℂ)‖+o.im*Real.exp L
  let Y := o.im/Real.exp L
  let A := (1/Y)^2*(4*X/Y+8*X)*B
  have hH : 0<H := localDisplacementScale_pos o L
  have hB : 0<B := displacementDenominatorBound_pos o L D
  have hi := o.im_pos
  have hX : 0≤X := by dsimp only [X]; positivity
  have hY : 0<Y := by dsimp only [Y]; positivity
  have hV : 0≤V := ENNReal.toReal_nonneg
  have hA : 0≤A := by dsimp only [A]; positivity
  have hQ : reflectedSublevelConstant o L D=A*H+V := rfl
  have hvol : volume (Metric.closedBall o L)=ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  rw [hQ]
  by_cases hr1 : r≤1
  · have harea := congruence_reflected_displacement_volume N γ (Metric.closedBall o L)
      X Y X B (H*r) hX hY hX hB.le (mul_pos hH hr)
      (fun z hz => (Complex.abs_re_le_norm (z:ℂ)).trans (norm_coe_le_on_ball o z L hz))
      (fun z hz => im_lower_on_ball o z L hz)
      (fun z hz => (Complex.abs_im_le_norm (z:ℂ)).trans (norm_coe_le_on_ball o z L hz))
      (fun z hz => diagonalOrbitSet_reflected_denominator_bound N o z L D hz γ hγ)
    apply (measure_mono (show {z∈Metric.closedBall o L | dist (γ•(J•z)) z<r}⊆
      {z∈Metric.closedBall o L | ‖(z:ℂ)-((γ•(J•z):ℍ):ℂ)‖<H*r} from ?_)).trans
      (harea.trans ?_)
    · rintro z ⟨hz,hzr⟩
      exact ⟨hz,(euclidean_displacement_le_hyperbolic o z (γ•(J•z)) L hz
        (hzr.le.trans hr1)).trans_lt (mul_lt_mul_of_pos_left hzr hH)⟩
    · apply ENNReal.ofReal_le_ofReal
      have he : (1/Y)^2*((4*X/Y+8*X)*(B*(H*r)))=A*H*r := by dsimp only [A]; ring
      rw [he]
      nlinarith
  · have hlarge : 1<r := lt_of_not_ge hr1
    apply ((measure_mono (show {z∈Metric.closedBall o L | dist (γ•(J•z)) z<r}⊆
      Metric.closedBall o L from fun _ hz => hz.1)).trans_eq hvol).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hlarge.le hV,mul_nonneg hA hH.le]

/-- Absolute integrability of the actual reflected displacement singularity,
with a bound uniform in the entire prescribed finite orbit set. -/
theorem diagonalOrbitSet_reflected_inverse_sqrt_integral (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) :
    IntegrableOn (fun z : ℍ => 1/Real.sqrt (dist (γ•(J•z)) z)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ•(J•z)) z))≤
      Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L D) := by
  have hm : Measurable (fun z : ℍ => dist (γ•(J•z)) z) :=
    (((continuous_const_smul γ).comp (continuous_const_smul J)).dist continuous_id).measurable
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ•(J•z)) z) hm (fun _ => dist_nonneg)
    (volume.real (Metric.closedBall o L)) (reflectedSublevelConstant o L D)
    ENNReal.toReal_nonneg (reflectedSublevelConstant_nonneg o L D)
  · rw [Measure.restrict_apply_univ]
    exact le_of_eq (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  · intro r hr
    rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ•(J•z)) z<r} from hm measurableSet_Iio)]
    convert diagonalOrbitSet_reflected_hyperbolic_sublevel N o L D γ hγ r hr using 2
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq,and_comm]

/-- The fixed set of each reflected branch has zero area, including J itself. -/
theorem diagonalOrbitSet_reflected_displacement_pos_ae (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall o L),0<dist (γ•(J•z)) z := by
  have hm : Measurable (fun z : ℍ => dist (γ•(J•z)) z) :=
    (((continuous_const_smul γ).comp (continuous_const_smul J)).dist continuous_id).measurable
  have hz := measure_zero_of_linear_sublevels (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ•(J•z)) z) (reflectedSublevelConstant o L D)
    (by
      intro r hr
      rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ•(J•z)) z<r} from hm measurableSet_Iio)]
      convert diagonalOrbitSet_reflected_hyperbolic_sublevel N o L D γ hγ r hr using 2
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq,and_comm])
  rw [ae_iff]
  convert hz using 2
  ext z
  simp only [mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h dist_nonneg,fun h => h.le⟩

#print axioms diagonalOrbitSet_reflected_denominator_bound
#print axioms reflectedSublevelConstant_nonneg
#print axioms diagonalOrbitSet_reflected_hyperbolic_sublevel
#print axioms diagonalOrbitSet_reflected_inverse_sqrt_integral
#print axioms diagonalOrbitSet_reflected_displacement_pos_ae

end QuantitativeMaass
