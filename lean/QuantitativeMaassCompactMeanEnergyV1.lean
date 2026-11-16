module

public import QuantitativeMaassCompactFullInputV1
public import QuantitativeMaassCappedCompactTraceV1
public import QuantitativeMaassCylinderCenteringErrorV1
public import QuantitativeMaassCylinderMeanHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

theorem compact_input_column_mean_eq
    (P : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) (z : ℍ) :
    P (cylinderTimeColumn f hc he R hR hs z)-P (cylinderCenteredTimeColumn f hc he R hR hs z)=
      P (∫ u in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (u+ᵥz)) := by
  rw [cylinderCenteredTimeColumn,map_sub]
  abel

/-- Global energy of the horizontal mean after a compact input cut, with
an explicit geometric coefficient multiplying the off-diagonal amplitude. -/
theorem compact_input_column_mean_energy (hr : ∀ t,star (f t)=f t)
    {a : ℝ} (ha : 0<a) (b : ℝ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
    let K := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
    (∫ z,‖P (cylinderTimeColumn f hc he R hR hs z)-
      P (cylinderCenteredTimeColumn f hc he R hR hs z)‖^2 ∂quotientMeasure 0)≤
      max 0 (b*Real.exp R)*(C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*volume.real K := by
  intro P K
  let d := fun z => P (cylinderTimeColumn f hc he R hR hs z)-
    P (cylinderCenteredTimeColumn f hc he R hR hs z)
  let E := C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2))
  have hE : 0≤E := by dsimp only [E]; positivity
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))
  have hd : Continuous d :=
    (P.continuous.comp (cylinderAbelColumn_continuous _ _ R hR _)).sub
      (P.continuous.comp (cylinderCenteredTimeColumn_continuous f hc he R hR hs))
  have hstrip : ∀ᵐ z ∂quotientMeasure 0,z∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  have hsupport : (fun z => ‖d z‖^2)=ᵐ[quotientMeasure 0] K.indicator (fun z => ‖d z‖^2) := by
    filter_upwards [hstrip] with z hz
    by_cases hzK : z∈K
    · exact (indicator_of_mem hzK (fun z => ‖d z‖^2)).symm
    · have hout : ¬(a*Real.exp (-R)≤z.im ∧ z.im≤b*Real.exp R) :=
        fun hh => hzK ⟨⟨hz.1,hz.2.le⟩,hh⟩
      have hzero : d z=0 := by
        dsimp only [d]
        rw [cylinderTimeColumn_compact_input_zero f hc he R hR hs ha b z hout,
          cylinderCenteredTimeColumn_compact_input_zero f hc he R hR hs ha b z hout,sub_self]
      rw [hzero,norm_zero,zero_pow (by decide : 2≠0),indicator_of_notMem hzK]
  change (∫ z,‖d z‖^2 ∂quotientMeasure 0)≤_
  rw [integral_congr_ae hsupport,integral_indicator hK.measurableSet,
    cylinder_rectangle_measure _ _ (mul_pos ha (Real.exp_pos _))]
  have hbound : ∀ᵐ z ∂volume.restrict K,‖d z‖^2≤max 0 (b*Real.exp R)*E := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hnorm : ‖d z‖≤‖∫ u in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (u+ᵥz)‖ := by
      dsimp only [d]
      rw [compact_input_column_mean_eq f hc he R hR hs]
      simpa only [one_mul] using P.le_of_opNorm_le (AsymptoticRegionL2.projection_norm_le _ _ _)
        (∫ u in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (u+ᵥz))
    have hh := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (cylinderTimeColumn_mean_energy_bound f hc he hr R hR hs C hC hb z)
    exact hh.trans (mul_le_mul_of_nonneg_right (hz.2.2.trans (le_max_right _ _)) hE)
  calc
    _ ≤ ∫ _z in K,max 0 (b*Real.exp R)*E := integral_mono_ae
      ((hd.norm.pow 2).continuousOn.integrableOn_compact hK)
      (continuous_const.continuousOn.integrableOn_compact hK) hbound
    _ = _ := by
      rw [integral_const]
      simp only [E,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
      ring

#print axioms cylinderTimeColumn_compact_input_memLp
#print axioms compact_input_column_mean_eq
#print axioms compact_input_column_mean_energy
end QuantitativeMaass
