module

public import QuantitativeMaassColumnHeightLocalizationV1
public import QuantitativeMaassCompactFullInputV1
public import QuantitativeMaassCylinderBranchTraceV1

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

/-- The same output support holds after the actual horizontal mean is
subtracted, because translations preserve height. -/
theorem cylinderCenteredTimeColumn_compact_input_zero {a : ℝ} (ha : 0<a) (b : ℝ)
    (z : ℍ) (hz : ¬(a*Real.exp (-R)≤z.im ∧ z.im≤b*Real.exp R)) :
    AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
      (cylinderCenteredTimeColumn f hc he R hR hs z)=0 := by
  let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
    (upperRectangle_compact _ _ _ _ ha).measurableSet
  have hi : IntegrableOn (fun u : ℝ => cylinderTimeColumn f hc he R hR hs (u+ᵥz)) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply (cylinderAbelColumn_continuous _ _ R hR _).comp
    apply continuous_induced_rng.mpr
    fun_prop
  change P (cylinderTimeColumn f hc he R hR hs z-
    ∫ u in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (u+ᵥz))=0
  rw [map_sub,←P.integral_comp_comm hi,cylinderTimeColumn_compact_input_zero f hc he R hR hs ha b z hz]
  have hi0 : (∫ u in Icc (0:ℝ) 1,P (cylinderTimeColumn f hc he R hR hs (u+ᵥz)))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with u
    exact cylinderTimeColumn_compact_input_zero f hc he R hR hs ha b (u+ᵥz) (by simpa using hz)
  rw [hi0,sub_zero]

/-- The compact-input centered columns have finite energy on the entire
translation cylinder. This supplies the integrability for enlarging the trace
integration domain. -/
theorem cylinderCenteredTimeColumn_compact_input_memLp {a : ℝ} (ha : 0<a) (b : ℝ) :
    MemLp (fun z => AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
      (cylinderCenteredTimeColumn f hc he R hR hs z)) 2 (quotientMeasure 0) := by
  let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
    (upperRectangle_compact _ _ _ _ ha).measurableSet
  let c := fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z)
  let K := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))
  have hcC : Continuous c := P.continuous.comp (cylinderCenteredTimeColumn_continuous f hc he R hR hs)
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
    apply cylinderCenteredTimeColumn_compact_input_zero f hc he R hR hs ha b z
    intro hheight
    exact hzK ⟨⟨hz.1,hz.2.le⟩,hheight⟩

/-- Positivity permits enlarging a retained output set only after the actual
compact-input column integrability has been established. -/
theorem compact_input_centered_trace_restrict_le {a : ℝ} (ha : 0<a) (b : ℝ)
    (S : Set ℍ) (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hT : T.IsPositive) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
    columnLinearTrace ((quotientMeasure 0).restrict S)
      (fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z)) T≤
    columnLinearTrace (quotientMeasure 0)
      (fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z)) T := by
  intro P
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall (fun z => hT.re_inner_nonneg_left _))
    (columnLinearTrace_integrable _ _
      (cylinderCenteredTimeColumn_compact_input_memLp f hc he R hR hs ha b) T)

#print axioms cylinderTimeColumn_compact_input_zero
#print axioms cylinderCenteredTimeColumn_compact_input_zero
#print axioms cylinderCenteredTimeColumn_compact_input_memLp
#print axioms compact_input_centered_trace_restrict_le
end QuantitativeMaass
