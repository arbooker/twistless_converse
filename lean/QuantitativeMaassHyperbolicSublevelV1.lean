module

public import QuantitativeMaassDisplacementSublevelV1
public import QuantitativeMaassSublevelIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousConstSMul (gamma N) ℍ :=
  ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩

theorem exp_sub_one_le_linear (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x-1≤Real.exp 1*x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero x)] at h
  have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx1) hx
  nlinarith

def localDisplacementScale (o : ℍ) (L : ℝ) : ℝ := o.im*Real.exp L*Real.exp 1

theorem localDisplacementScale_pos (o : ℍ) (L : ℝ) : 0<localDisplacementScale o L := by
  unfold localDisplacementScale
  positivity

/-- Uniform conversion of small hyperbolic displacement to Euclidean displacement.
Only the height of the centre, not the image point, enters the constant. -/
theorem euclidean_displacement_le_hyperbolic (o z w : ℍ) (L : ℝ)
    (hz : dist z o≤L) (hzw : dist w z≤1) :
    ‖(z:ℂ)-(w:ℂ)‖≤localDisplacementScale o L*dist w z := by
  have hheight : z.im≤o.im*Real.exp L :=
    (im_le_im_mul_exp_dist z o).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hz) o.im_pos.le)
  calc
    _ = dist (w:ℂ) (z:ℂ) := by rw [dist_comm,dist_eq_norm]
    _ ≤ z.im*(Real.exp (dist w z)-1) := dist_coe_le w z
    _ ≤ z.im*(Real.exp 1*dist w z) :=
      mul_le_mul_of_nonneg_left (exp_sub_one_le_linear _ dist_nonneg hzw) z.im_pos.le
    _ ≤ (o.im*Real.exp L)*(Real.exp 1*dist w z) :=
      mul_le_mul_of_nonneg_right hheight (by positivity)
    _ = _ := by unfold localDisplacementScale;ring

/-- The radius multiplier and cutoff are explicit; the area constant is
independent of the level and of the chosen element in the finite orbit set. -/
def hyperbolicSublevelConstant (o : ℍ) (L D : ℝ) : ℝ :=
  (1/(o.im/Real.exp L))^2*
    (2*Real.pi*displacementDenominatorBound o L D+
      Real.pi*(displacementDenominatorBound o L D)^2)*localDisplacementScale o L+
  volume.real (Metric.closedBall o L)*
    (1+localDisplacementScale o L+
      localDisplacementScale o L*displacementDenominatorBound o L D)

theorem hyperbolicSublevelConstant_nonneg (o : ℍ) (L D : ℝ) :
    0≤hyperbolicSublevelConstant o L D := by
  have hH := localDisplacementScale_pos o L
  have hD := displacementDenominatorBound_pos o L D
  unfold hyperbolicSublevelConstant
  positivity

/-- A global linear small-displacement area bound for every original
nonidentity congruence element in the specified orbit set. -/
theorem diagonalOrbitSet_hyperbolic_sublevel (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) (hne : γ≠1)
    (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (γ•z) z<r}≤
      ENNReal.ofReal (hyperbolicSublevelConstant o L D*r) := by
  let H := localDisplacementScale o L
  let B := displacementDenominatorBound o L D
  let V := volume.real (Metric.closedBall o L)
  let A := (1/(o.im/Real.exp L))^2*(2*Real.pi*B+Real.pi*B^2)
  let T := 1+H+H*B
  have hH : 0<H := localDisplacementScale_pos o L
  have hB : 0<B := displacementDenominatorBound_pos o L D
  have hV : 0≤V := ENNReal.toReal_nonneg
  have hA : 0≤A := by dsimp only [A];positivity
  have hT : 0<T := by dsimp only [T];positivity
  have hQ : hyperbolicSublevelConstant o L D=A*H+V*T := rfl
  have hvol : volume (Metric.closedBall o L)=ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  rw [hQ]
  by_cases hsmall : r*T≤1
  · have hr1 : r≤1 := by
      have h1 : 1≤T := by dsimp only [T];nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hr.le]
    have hHr : H*r≤1 := by
      have hh : H≤T := by dsimp only [T];nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh hr.le]
    have hHrB : (H*r)*B≤1 := by
      have hh : H*B≤T := by dsimp only [T];linarith
      nlinarith [mul_le_mul_of_nonneg_left hh hr.le]
    have harea := congruence_displacement_sublevel_volume N γ hne (Metric.closedBall o L)
      B (H*r) (o.im/Real.exp L) hB.le (mul_pos hH hr) hHr hHrB (by positivity)
      (fun z hz => im_lower_on_ball o z L hz)
      (fun z hz => diagonalOrbitSet_denominator_bound N o z L D hz γ hγ)
    apply (measure_mono (show {z∈Metric.closedBall o L | dist (γ•z) z<r}⊆
      {z∈Metric.closedBall o L | ‖(z:ℂ)-((γ•z : ℍ):ℂ)‖<H*r} from ?_)).trans
      (harea.trans ?_)
    · rintro z ⟨hz,hzr⟩
      refine ⟨hz,?_⟩
      exact (euclidean_displacement_le_hyperbolic o z (γ•z) L hz
        (hzr.le.trans hr1)).trans_lt (mul_lt_mul_of_pos_left hzr hH)
    · apply ENNReal.ofReal_le_ofReal
      rw [← mul_assoc]
      change A*(H*r)≤(A*H+V*T)*r
      nlinarith [mul_nonneg hV hT.le]
  · have hlarge : 1<r*T := lt_of_not_ge hsmall
    apply ((measure_mono (show {z∈Metric.closedBall o L | dist (γ•z) z<r}⊆
      Metric.closedBall o L from fun _ hz => hz.1)).trans_eq hvol).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hlarge.le hV,mul_nonneg hA hH.le]

/-- The original displacement singularity is absolutely integrable, uniformly
in nonidentity elements of the finite orbit set. -/
theorem diagonalOrbitSet_inverse_sqrt_integral (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) (hne : γ≠1) :
    IntegrableOn (fun z : ℍ => 1/Real.sqrt (dist (γ•z) z)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ•z) z))≤
      Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L D) := by
  have hm : Measurable (fun z : ℍ => dist (γ•z) z) :=
    ((continuous_const_smul γ).dist continuous_id).measurable
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ•z) z) hm (fun _ => dist_nonneg)
    (volume.real (Metric.closedBall o L)) (hyperbolicSublevelConstant o L D)
    ENNReal.toReal_nonneg (hyperbolicSublevelConstant_nonneg o L D)
  · rw [Measure.restrict_apply_univ]
    exact le_of_eq (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  · intro r hr
    rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ•z) z<r} from hm measurableSet_Iio)]
    convert diagonalOrbitSet_hyperbolic_sublevel N o L D γ hγ hne r hr using 2
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq,and_comm]

/-- Fixed points of each original nonidentity element form a null set on the
whole centre ball, including elliptic elements. -/
theorem diagonalOrbitSet_displacement_pos_ae (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) (hne : γ≠1) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall o L),0<dist (γ•z) z := by
  have hm : Measurable (fun z : ℍ => dist (γ•z) z) :=
    ((continuous_const_smul γ).dist continuous_id).measurable
  have hz := measure_zero_of_linear_sublevels (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ•z) z) (hyperbolicSublevelConstant o L D)
    (by
      intro r hr
      rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ•z) z<r} from hm measurableSet_Iio)]
      convert diagonalOrbitSet_hyperbolic_sublevel N o L D γ hγ hne r hr using 2
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq,and_comm])
  rw [ae_iff]
  convert hz using 2
  ext z
  simp only [mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h dist_nonneg,fun h => h.le⟩

#print axioms exp_sub_one_le_linear
#print axioms localDisplacementScale_pos
#print axioms euclidean_displacement_le_hyperbolic
#print axioms hyperbolicSublevelConstant_nonneg
#print axioms diagonalOrbitSet_hyperbolic_sublevel
#print axioms diagonalOrbitSet_inverse_sqrt_integral
#print axioms diagonalOrbitSet_displacement_pos_ae

end QuantitativeMaass
