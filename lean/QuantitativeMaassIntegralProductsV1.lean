module

public import QuantitativeMaassIntegralDisplacementV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal MatrixGroups

namespace QuantitativeMaass

/-- Positive integral matrices compose as their actual Möbius maps. -/
theorem positiveIntegralGL_mul (M K : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (hK : 0<K.det) (hMK : 0<(M*K).det) :
    positiveIntegralGL (M*K) hMK=positiveIntegralGL M hM*positiveIntegralGL K hK := by
  apply Units.ext
  change (M*K).map (Int.castRingHom ℝ)=M.map (Int.castRingHom ℝ)*K.map (Int.castRingHom ℝ)
  exact Matrix.map_mul

theorem positiveIntegralGL_of_SL (s : SL(2,ℤ)) (hs : 0<s.val.det) :
    positiveIntegralGL s.val hs=SpecialLinearGroup.mapGL ℝ s := by
  apply Units.ext
  rfl

/-- Left multiplication by an integral congruence representative preserves
the positive determinant of the fixed Hecke word matrix. -/
theorem congruence_product_det (N : ℕ) (γ : gamma N) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ((representative γ).val*M).det=M.det := by
  rw [Matrix.det_mul,(representative γ).property,one_mul]

/-- The integral product used in the sublevel estimate is the actual
congruence action followed by the actual fixed rational transformation. -/
theorem congruence_positiveIntegralGL_action (N : ℕ) (γ : gamma N)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (hprod : 0<((representative γ).val*M).det) (z : ℍ) :
    positiveIntegralGL ((representative γ).val*M) hprod • z=
      γ • (positiveIntegralGL M hM • z) := by
  have hg : 0<(representative γ).val.det := by rw [(representative γ).property]; norm_num
  rw [positiveIntegralGL_mul _ _ hg hM hprod,positiveIntegralGL_of_SL,mul_smul]
  change representative γ • (positiveIntegralGL M hM • z)=_
  rw [← integralLabel_action,representative_label]
  rfl

/-- Uniform entry bound for a two-by-two integral matrix product. -/
theorem integralMatrix_product_entry_bound (M K : Matrix (Fin 2) (Fin 2) ℤ)
    (A B : ℝ) (hA : 0≤A) (_hB : 0≤B)
    (hm : ∀ i j,|(M i j:ℝ)|≤A) (hk : ∀ i j,|(K i j:ℝ)|≤B) (i j : Fin 2) :
    |((M*K) i j:ℝ)|≤2*A*B := by
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul]
  calc
    _ ≤ |(M i 0:ℝ)*(K 0 j:ℝ)| + |(M i 1:ℝ)*(K 1 j:ℝ)| := abs_add_le _ _
    _ = |(M i 0:ℝ)| * |(K 0 j:ℝ)| + |(M i 1:ℝ)| * |(K 1 j:ℝ)| := by rw [abs_mul,abs_mul]
    _ ≤ A*B+A*B := add_le_add
      (mul_le_mul (hm i 0) (hk 0 j) (abs_nonneg _) hA)
      (mul_le_mul (hm i 1) (hk 1 j) (abs_nonneg _) hA)
    _ = _ := by ring

/-- A fixed matrix costs a fixed multiplicative denominator factor across
the entire finite congruence orbit set. -/
theorem congruence_product_denominator_bound (N : ℕ) (o z : ℍ) (L D C : ℝ)
    (hC : 0≤C) (hz : dist z o≤L) (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hm : ∀ i j,|(M i j:ℝ)|≤C) :
    ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*(z:ℂ)+((representative γ).val*M) 1 1‖≤
      2*C*displacementDenominatorBound o L D := by
  let E := Real.exp (D/2+dist o I)
  have he : 0≤E := (Real.exp_pos _).le
  have hb (i j : Fin 2) : |(((representative γ).val*M) i j:ℝ)|≤2*E*C :=
    integralMatrix_product_entry_bound _ M E C he hC (diagonalOrbitSet_entry_bound N o D γ hγ) hm i j
  have hcast (a : ℤ) : ‖(a:ℂ)‖=|(a:ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*(z:ℂ)‖+
        ‖(((representative γ).val*M) 1 1:ℂ)‖ := norm_add_le _ _
    _ = |(((representative γ).val*M) 1 0:ℝ)| * ‖(z:ℂ)‖+
        |(((representative γ).val*M) 1 1:ℝ)| := by rw [norm_mul,hcast,hcast]
    _ ≤ (2*E*C)*(‖(o:ℂ)‖+o.im*Real.exp L)+(2*E*C) :=
      add_le_add (mul_le_mul (hb 1 0) (norm_coe_le_on_ball o z L hz) (norm_nonneg _) (by positivity)) (hb 1 1)
    _ = _ := by unfold displacementDenominatorBound;dsimp only [E];ring

/-- Absorb the fixed matrix denominator cost into an explicit additive
shift of the original geometric radius parameter. -/
theorem displacementDenominatorBound_shift (o : ℍ) (L D C : ℝ) (hC : 0<C) :
    displacementDenominatorBound o L (D+2*Real.log (2*C))=
      2*C*displacementDenominatorBound o L D := by
  unfold displacementDenominatorBound
  rw [show (D+2*Real.log (2*C))/2+dist o I=Real.log (2*C)+(D/2+dist o I) by ring,
    Real.exp_add,Real.exp_log (by positivity : 0<2*C)]
  ring

/-- Uniform small-return geometry for every nonscalar actual product
of a congruence representative with a fixed positive integral matrix. -/
theorem congruence_product_hyperbolic_sublevel (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hm : ∀ i j,|(M i j:ℝ)|≤C)
    (hne : ((representative γ).val*M) 1 0≠0 ∨
      ((representative γ).val*M) 1 1≠((representative γ).val*M) 0 0 ∨
      ((representative γ).val*M) 0 1≠0) (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (γ • (positiveIntegralGL M hM • z)) z<r}≤
      ENNReal.ofReal (hyperbolicSublevelConstant o L (D+2*Real.log (2*C))*r) := by
  have hp : 0<((representative γ).val*M).det := by rw [congruence_product_det];exact hM
  have hb (z : ℍ) (hz : z∈Metric.closedBall o L) :
      ‖((((representative γ).val*M) 1 0:ℤ):ℂ)*(z:ℂ)+((representative γ).val*M) 1 1‖≤
        displacementDenominatorBound o L (D+2*Real.log (2*C)) := by
    rw [displacementDenominatorBound_shift o L D C hC]
    exact congruence_product_denominator_bound N o z L D C hC.le hz γ hγ M hm
  have hh := positiveIntegralGL_hyperbolic_sublevel _ hp hne o L (D+2*Real.log (2*C)) hb r hr
  simpa only [congruence_positiveIntegralGL_action N γ M hM hp] using hh

/-- Uniform absolute integrability of the inverse-square-root displacement
for every nonscalar correspondence product in the prescribed orbit family. -/
theorem congruence_product_inverse_sqrt_integral (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤C)
    (hne : ((representative γ).val*M) 1 0≠0 ∨
      ((representative γ).val*M) 1 1≠((representative γ).val*M) 0 0 ∨
      ((representative γ).val*M) 0 1≠0) :
    IntegrableOn (fun z : ℍ => 1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • z)) z)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • z)) z))≤
      Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (D+2*Real.log (2*C))) := by
  have hm : Measurable (fun z : ℍ => dist (γ • (positiveIntegralGL M hM • z)) z) :=
    (((AsymptoticRationalBranches.action_continuous γ.val).comp
      (continuous_const_smul (positiveIntegralGL M hM))).dist continuous_id).measurable
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ • (positiveIntegralGL M hM • z)) z) hm (fun _ => dist_nonneg)
    (volume.real (Metric.closedBall o L)) (hyperbolicSublevelConstant o L (D+2*Real.log (2*C)))
    ENNReal.toReal_nonneg (hyperbolicSublevelConstant_nonneg o L (D+2*Real.log (2*C)))
  · rw [Measure.restrict_apply_univ]
    exact le_of_eq (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  · intro r hr
    rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ • (positiveIntegralGL M hM • z)) z<r} from hm measurableSet_Iio)]
    convert congruence_product_hyperbolic_sublevel N o L D C hC γ hγ M hM hentry hne r hr using 2
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq,and_comm]

/-- Nonscalar integral correspondence products have null fixed-point sets
on the entire centre ball, including elliptic products. -/
theorem congruence_product_displacement_pos_ae (N : ℕ) (o : ℍ) (L D C : ℝ) (hC : 0<C)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤C)
    (hne : ((representative γ).val*M) 1 0≠0 ∨
      ((representative γ).val*M) 1 1≠((representative γ).val*M) 0 0 ∨
      ((representative γ).val*M) 0 1≠0) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall o L),0<dist (γ • (positiveIntegralGL M hM • z)) z := by
  have hm : Measurable (fun z : ℍ => dist (γ • (positiveIntegralGL M hM • z)) z) :=
    (((AsymptoticRationalBranches.action_continuous γ.val).comp
      (continuous_const_smul (positiveIntegralGL M hM))).dist continuous_id).measurable
  have hz := measure_zero_of_linear_sublevels (volume.restrict (Metric.closedBall o L))
    (fun z => dist (γ • (positiveIntegralGL M hM • z)) z) (hyperbolicSublevelConstant o L (D+2*Real.log (2*C)))
    (by
      intro r hr
      rw [Measure.restrict_apply (show MeasurableSet {z : ℍ | dist (γ • (positiveIntegralGL M hM • z)) z<r} from hm measurableSet_Iio)]
      convert congruence_product_hyperbolic_sublevel N o L D C hC γ hγ M hM hentry hne r hr using 2
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq,and_comm])
  rw [ae_iff]
  convert hz using 2
  ext z
  simp only [mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h dist_nonneg,fun h => h.le⟩

#print axioms congruence_product_inverse_sqrt_integral
#print axioms congruence_product_displacement_pos_ae

#print axioms positiveIntegralGL_mul
#print axioms positiveIntegralGL_of_SL
#print axioms congruence_product_det
#print axioms congruence_positiveIntegralGL_action
#print axioms integralMatrix_product_entry_bound
#print axioms congruence_product_denominator_bound
#print axioms displacementDenominatorBound_shift
#print axioms congruence_product_hyperbolic_sublevel

end QuantitativeMaass
