module

public import QuantitativeMaassCylinderKernelSupportV1
public import QuantitativeMaassCylinderBranchTraceV1
public import QuantitativeMaassCylinderRectangleMeasureV1
public import AsymptoticRegionL2V1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

private theorem height_bounds_of_log_bound (a b R : ℝ) (z w : ℍ)
    (hw : a≤w.im ∧ w.im≤b) (h : |Real.log w.im-Real.log z.im|≤R) :
    a*Real.exp (-R)≤z.im ∧ z.im≤b*Real.exp R := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor
  · calc
      _ ≤ w.im*Real.exp (-R) := mul_le_mul_of_nonneg_right hw.1 (Real.exp_pos _).le
      _ = Real.exp (Real.log w.im-R) := by rw [Real.exp_sub,Real.exp_log w.im_pos,Real.exp_neg]; rfl
      _ ≤ Real.exp (Real.log z.im) := Real.exp_le_exp.mpr (by linarith)
      _ = z.im := Real.exp_log z.im_pos
  · calc
      z.im = Real.exp (Real.log z.im) := (Real.exp_log z.im_pos).symm
      _ ≤ Real.exp (Real.log w.im+R) := Real.exp_le_exp.mpr (by linarith)
      _ = w.im*Real.exp R := by rw [Real.exp_add,Real.exp_log w.im_pos]
      _ ≤ _ := mul_le_mul_of_nonneg_right hw.2 (Real.exp_pos _).le

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

/-- Compact input restriction forces the output column to vanish outside
the propagated height interval. -/
theorem cylinderTimeColumn_compact_input_zero {a : ℝ} (ha : 0<a) (b : ℝ)
    (z : ℍ) (hz : ¬(a*Real.exp (-R)≤z.im ∧ z.im≤b*Real.exp R)) :
    AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
      (cylinderTimeColumn f hc he R hR hs z)=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
  filter_upwards [cylinderAbelColumn_coeFn (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs) z] with w hcol hw
  change cylinderTimeColumn f hc he R hR hs z w=_ at hcol
  rw [hcol]
  by_contra hn
  have hh : |Real.log w.im-Real.log z.im|≤R :=
    le_of_not_gt (fun ht => hn (cylinderRadialKernel_log_zero _ R hR
      (abelProfile_support _ _ (evenCoshLift_support_of_time_support f R hR hs)) z w ht))
  exact hz (height_bounds_of_log_bound a b R z w hw.2 hh)

theorem cylinderTimeColumn_compact_input_memLp {a : ℝ} (ha : 0<a) (b : ℝ) :
    MemLp (fun z => AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
      (cylinderTimeColumn f hc he R hR hs z)) 2 (quotientMeasure 0) := by
  let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
    (upperRectangle_compact _ _ _ _ ha).measurableSet
  let c := fun z => P (cylinderTimeColumn f hc he R hR hs z)
  let K := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))
  have hcC : Continuous c := P.continuous.comp (cylinderAbelColumn_continuous _ _ R hR _)
  have hi : MemLp (K.indicator c) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (compact_column_memLp c hcC K hK)
  change MemLp c 2 (quotientMeasure 0)
  apply (congrArg (fun μ : Measure ℍ => MemLp c 2 μ) translation_quotient_measure).mpr
  apply (hi.restrict strip).ae_eq
  filter_upwards [ae_restrict_mem strip_measurable] with z hz
  by_cases hzK : z∈K
  · exact indicator_of_mem hzK _
  · rw [indicator_of_notMem hzK]
    symm
    apply cylinderTimeColumn_compact_input_zero f hc he R hR hs ha b z
    intro hheight
    exact hzK ⟨⟨hz.1,hz.2.le⟩,hheight⟩

#print axioms cylinderTimeColumn_compact_input_zero
#print axioms cylinderTimeColumn_compact_input_memLp

end QuantitativeMaass
