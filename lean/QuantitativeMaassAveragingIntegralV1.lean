module

public import QuantitativeMaassAveragingDenominatorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticMobiusFold
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Explicit linear sublevel constant for one real averaging parameter. -/
def averagingSublevelConstant (B X Y : ℝ) (z : ℍ) : ℝ :=
  1+4*(3*B^2*(‖(z:ℂ)‖+1))*localDisplacementScale z 0/((1/(B*(1+(X+1)/Y)))^2)

theorem averagingSublevelConstant_nonneg (B X Y : ℝ) (z : ℍ) :
    0≤averagingSublevelConstant B X Y z := by
  have hh := localDisplacementScale_pos z 0
  unfold averagingSublevelConstant
  positivity

/-- Absolute integrability of the genuine displacement singularity for
one averaging insertion, with no integrability premise. -/
theorem averaging_displacement_inverse_sqrt (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im) :
    IntegrableOn (fun u : ℝ => 1/Real.sqrt (dist (G • (u+ᵥ(H•z))) z)) (Icc (0:ℝ) 1) ∧
    (∫ u in Icc (0:ℝ) 1,1/Real.sqrt (dist (G • (u+ᵥ(H•z))) z))≤
      Real.pi*(1+averagingSublevelConstant B X Y z) := by
  have hm : Measurable (fun u : ℝ => dist (G • (u+ᵥ(H•z))) z) :=
    (((continuous_const_smul G).comp (cylinder_vadd_continuous (H•z))).dist continuous_const).measurable
  apply inverse_sqrt_integrable_of_sublevel (volume.restrict (Icc (0:ℝ) 1))
    (fun u : ℝ => dist (G • (u+ᵥ(H•z))) z) hm (fun _ => dist_nonneg)
    1 (averagingSublevelConstant B X Y z) (by norm_num) (averagingSublevelConstant_nonneg B X Y z)
  · rw [Measure.restrict_apply_univ,Real.volume_Icc]
    norm_num
  · intro r hr
    rw [Measure.restrict_apply (show MeasurableSet {u : ℝ | dist (G • (u+ᵥ(H•z))) z<r} from hm measurableSet_Iio)]
    unfold averagingSublevelConstant
    convert averaging_hyperbolic_parameter_sublevel_explicit G H hG hH B hB hGb hHb z X Y hX hY hx hy r hr using 2
    ext u
    simp only [mem_inter_iff,mem_ofPred_eq,and_comm]

/-- Identity returns under an averaging insertion form a null parameter
set, so there is no identity main term after integration. -/
theorem averaging_displacement_pos_ae (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),(0 : ℝ) < dist (G • (u+ᵥ(H•z))) z := by
  have hm : Measurable (fun u : ℝ => dist (G • (u+ᵥ(H•z))) z) :=
    (((continuous_const_smul G).comp (cylinder_vadd_continuous (H•z))).dist continuous_const).measurable
  have hz := measure_zero_of_linear_sublevels (volume.restrict (Icc (0:ℝ) 1))
    (fun u : ℝ => dist (G • (u+ᵥ(H•z))) z) (averagingSublevelConstant B X Y z) (by
      intro r hr
      rw [Measure.restrict_apply (show MeasurableSet {u : ℝ | dist (G • (u+ᵥ(H•z))) z<r} from hm measurableSet_Iio)]
      unfold averagingSublevelConstant
      convert averaging_hyperbolic_parameter_sublevel_explicit G H hG hH B hB hGb hHb z X Y hX hY hx hy r hr using 2
      ext u
      simp only [mem_inter_iff,mem_ofPred_eq,and_comm])
  rw [ae_iff]
  convert hz using 2
  ext u
  simp only [mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h dist_nonneg,fun h => h.le⟩

/-- The actual radial kernel profile is absolutely integrable through
an averaging insertion, at the off-diagonal amplitude scale. -/
theorem averaging_profile_integral_bound (G H : GL (Fin 2) ℝ)
    (hG : G.val.det=1) (hH : H.val.det=1) (B : ℝ) (hB : 0<B)
    (hGb : ∀ i j,|G.val i j|≤B) (hHb : ∀ i j,|H.val i j|≤B)
    (z : ℍ) (X Y : ℝ) (hX : 0≤X) (hY : 0<Y) (hx : |z.re|≤X) (hy : Y≤z.im)
    (g : ℝ→ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun u : ℝ => g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))) (Icc (0:ℝ) 1) ∧
    (∫ u in Icc (0:ℝ) 1,‖g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))‖)≤
      C*(Real.pi*(1+averagingSublevelConstant B X Y z)) := by
  have hd : Continuous (fun u : ℝ => dist (G • (u+ᵥ(H•z))) z) :=
    ((continuous_const_smul G).comp (cylinder_vadd_continuous (H•z))).dist continuous_const
  have hi : IntegrableOn (fun u : ℝ => g (Real.cosh (dist (G • (u+ᵥ(H•z))) z))) (Icc (0:ℝ) 1) :=
    (hg.comp_continuous (Real.continuous_cosh.comp hd) (fun _ => Real.one_le_cosh _)).integrableOn_Icc
  obtain ⟨hj,hjb⟩ := averaging_displacement_inverse_sqrt G H hG hH B hB hGb hHb z X Y hX hY hx hy
  refine ⟨hi,?_⟩
  calc
    _≤∫ u in Icc (0:ℝ) 1,C*(1/Real.sqrt (dist (G • (u+ᵥ(H•z))) z)) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [averaging_displacement_pos_ae G H hG hH B hB hGb hHb z X Y hX hY hx hy] with u hu
      calc
        _≤C/Real.sqrt (Real.sinh (dist (G • (u+ᵥ(H•z))) z)) := hb _ hu
        _≤C/Real.sqrt (dist (G • (u+ᵥ(H•z))) z) := div_le_div_of_nonneg_left hC
          (Real.sqrt_pos.mpr hu) (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hu.le))
        _=_ := by ring
    _=C*(∫ u in Icc (0:ℝ) 1,1/Real.sqrt (dist (G • (u+ᵥ(H•z))) z)) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hjb hC

#print axioms averagingSublevelConstant_nonneg
#print axioms averaging_displacement_inverse_sqrt
#print axioms averaging_displacement_pos_ae
#print axioms averaging_profile_integral_bound

end QuantitativeMaass
