module

public import QuantitativeMaassIntegralReflectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Uniform linear sublevel area for every reflected congruence branch,
including the identity representative, for all positive radii. -/
theorem positiveIntegralGL_reflected_hyperbolic_sublevel
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (o : ℍ) (L D : ℝ)
    (hbound : ∀ z∈Metric.closedBall o L,
      ‖(M 1 0:ℂ)*((J•z:ℍ):ℂ)+M 1 1‖≤displacementDenominatorBound o L D)
    (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • (J•z)) z<r}≤
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
  · have harea := positiveIntegralGL_reflected_displacement_volume M hM (Metric.closedBall o L)
      X Y X B (H*r) hX hY hX hB.le (mul_pos hH hr)
      (fun z hz => (Complex.abs_re_le_norm (z:ℂ)).trans (norm_coe_le_on_ball o z L hz))
      (fun z hz => im_lower_on_ball o z L hz)
      (fun z hz => (Complex.abs_im_le_norm (z:ℂ)).trans (norm_coe_le_on_ball o z L hz))
      hbound
    apply (measure_mono (show {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • (J•z)) z<r}⊆
      {z∈Metric.closedBall o L | ‖(z:ℂ)-((positiveIntegralGL M hM • (J•z):ℍ):ℂ)‖<H*r} from ?_)).trans
      (harea.trans ?_)
    · rintro z ⟨hz,hzr⟩
      exact ⟨hz,(euclidean_displacement_le_hyperbolic o z (positiveIntegralGL M hM • (J•z)) L hz
        (hzr.le.trans hr1)).trans_lt (mul_lt_mul_of_pos_left hzr hH)⟩
    · apply ENNReal.ofReal_le_ofReal
      have he : (1/Y)^2*((4*X/Y+8*X)*(B*(H*r)))=A*H*r := by dsimp only [A]; ring
      rw [he]
      nlinarith
  · have hlarge : 1<r := lt_of_not_ge hr1
    apply ((measure_mono (show {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • (J•z)) z<r}⊆
      Metric.closedBall o L from fun _ hz => hz.1)).trans_eq hvol).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hlarge.le hV,mul_nonneg hA hH.le]

/-- A fixed matrix costs a fixed multiplicative denominator factor across
the entire finite congruence orbit set. -/
theorem congruence_product_reflected_denominator_bound (N : ℕ) (o z : ℍ) (L D C : ℝ)
    (hC : 0≤C) (hz : dist z o≤L) (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hm : ∀ i j,|(M i j:ℝ)|≤C) :
    ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*((J•z:ℍ):ℂ)+((representative γ).val*M) 1 1‖≤
      2*C*displacementDenominatorBound o L D := by
  let E := Real.exp (D/2+dist o I)
  have he : 0≤E := (Real.exp_pos _).le
  have hb (i j : Fin 2) : |(((representative γ).val*M) i j:ℝ)|≤2*E*C :=
    integralMatrix_product_entry_bound _ M E C he hC (diagonalOrbitSet_entry_bound N o D γ hγ) hm i j
  have hcast (a : ℤ) : ‖(a:ℂ)‖=|(a:ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*((J•z:ℍ):ℂ)‖+
        ‖(((representative γ).val*M) 1 1:ℂ)‖ := norm_add_le _ _
    _ = |(((representative γ).val*M) 1 0:ℝ)| * ‖(z:ℂ)‖+
        |(((representative γ).val*M) 1 1:ℝ)| := by rw [norm_mul,hcast,hcast,coe_J_smul,norm_neg,Complex.norm_conj]
    _ ≤ (2*E*C)*(‖(o:ℂ)‖+o.im*Real.exp L)+(2*E*C) :=
      add_le_add (mul_le_mul (hb 1 0) (norm_coe_le_on_ball o z L hz) (norm_nonneg _) (by positivity)) (hb 1 1)
    _ = _ := by unfold displacementDenominatorBound;dsimp only [E];ring

/-- Uniform small-return geometry for every reflected actual product
of a congruence representative with a fixed positive integral matrix. -/
theorem congruence_product_reflected_hyperbolic_sublevel (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hm : ∀ i j,|(M i j:ℝ)|≤C)
    (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (γ • (positiveIntegralGL M hM • (J•z))) z<r}≤
      ENNReal.ofReal (reflectedSublevelConstant o L (D+2*Real.log (2*C))*r) := by
  have hp : 0<((representative γ).val*M).det := by rw [congruence_product_det];exact hM
  have hb (z : ℍ) (hz : z∈Metric.closedBall o L) :
      ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*((J•z:ℍ):ℂ)+((representative γ).val*M) 1 1‖≤
        displacementDenominatorBound o L (D+2*Real.log (2*C)) := by
    rw [displacementDenominatorBound_shift o L D C hC]
    exact congruence_product_reflected_denominator_bound N o z L D C hC.le hz γ hγ M hm
  have hh := positiveIntegralGL_reflected_hyperbolic_sublevel _ hp o L (D+2*Real.log (2*C)) hb r hr
  simpa only [congruence_positiveIntegralGL_action N γ M hM hp] using hh

/-- Uniform absolute integrability of the inverse-square-root displacement
for every reflected correspondence product in the prescribed orbit family. -/
theorem congruence_product_reflected_inverse_sqrt_integral (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤C) :
    IntegrableOn (fun z : ℍ => 1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • (J•z))) z)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • (J•z))) z))≤
      Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (D+2*Real.log (2*C))) := by
  have hm : Measurable (fun z : ℍ => dist (γ • (positiveIntegralGL M hM • (J•z))) z) :=
    (((AsymptoticRationalBranches.action_continuous γ.val).comp
      ((continuous_const_smul (positiveIntegralGL M hM)).comp (continuous_const_smul J))).dist continuous_id).measurable
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ • (positiveIntegralGL M hM • (J•z))) z) hm (fun _ => dist_nonneg)
    (volume.real (Metric.closedBall o L)) (reflectedSublevelConstant o L (D+2*Real.log (2*C)))
    ENNReal.toReal_nonneg (reflectedSublevelConstant_nonneg o L (D+2*Real.log (2*C)))
  · rw [Measure.restrict_apply_univ]
    exact le_of_eq (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  · intro r hr
    rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ • (positiveIntegralGL M hM • (J•z))) z<r} from hm measurableSet_Iio)]
    convert congruence_product_reflected_hyperbolic_sublevel N o L D C hC γ hγ M hM hentry r hr using 2
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq,and_comm]

/-- Every reflected integral correspondence product has a null fixed-point
set on the centre ball. -/
theorem congruence_product_reflected_displacement_pos_ae (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤C) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall o L),0<dist (γ • (positiveIntegralGL M hM • (J•z))) z := by
  have hm : Measurable (fun z : ℍ => dist (γ • (positiveIntegralGL M hM • (J•z))) z) :=
    (((AsymptoticRationalBranches.action_continuous γ.val).comp
      ((continuous_const_smul (positiveIntegralGL M hM)).comp (continuous_const_smul J))).dist continuous_id).measurable
  have hz := measure_zero_of_linear_sublevels (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ • (positiveIntegralGL M hM • (J•z))) z) (reflectedSublevelConstant o L (D+2*Real.log (2*C)))
    (by
      intro r hr
      rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ • (positiveIntegralGL M hM • (J•z))) z<r} from hm measurableSet_Iio)]
      convert congruence_product_reflected_hyperbolic_sublevel N o L D C hC γ hγ M hM hentry r hr using 2
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq,and_comm])
  rw [ae_iff]
  convert hz using 2
  ext z
  simp only [mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h dist_nonneg,fun h => h.le⟩

#print axioms positiveIntegralGL_reflected_hyperbolic_sublevel
#print axioms congruence_product_reflected_denominator_bound
#print axioms congruence_product_reflected_hyperbolic_sublevel
#print axioms congruence_product_reflected_inverse_sqrt_integral
#print axioms congruence_product_reflected_displacement_pos_ae

end QuantitativeMaass
