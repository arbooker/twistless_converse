module

public import QuantitativeMaassCanonicalCompactRestrictionV1
public import QuantitativeArithmeticMaassSharpSmoothTraceV1
public import QuantitativeArithmeticMaassScheduledCollarEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCompactBranch
open scoped Topology ContDiff SchwartzMap
namespace QuantitativeMaass.AdmissibleScalarCover

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- The physical canonical trace, with its actual inverse metric and cap,
is exactly the new/sign projection applied after the sharp quotient transfer.
There is no identification with the different weighted range projection. -/
theorem physicalNewSignProjection_rectangle_trace
    {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    {R : ℝ} (hR : 0≤R) (a b : ℝ) (ha : 0<a) (hheight : δ*Real.exp (-R)≤a)
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : α→Lp ℂ 2 (quotientMeasure 0)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let J := ⌈(ν:ℝ)*R+1⌉₊
    let K := ∑ n ∈ Finset.Icc (-(J:ℤ)) (J:ℤ),
      LogBands.inverse (quotientMeasure 0) (fun z => Real.log (cappedHeightWeight δ ν z))
        (Real.measurable_log.comp (cap_continuous δ ν).measurable) n
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
    let D := (cover.metric hδ hν).change.symm.toContinuousLinearMap
    let A := boundedCrossQuotientLocalization N 0 S hS (fun _ => (1:ℂ))
      aestronglyMeasurable_const (A:=1) (Filter.Eventually.of_forall (fun _ => by simp))
    columnLinearTrace μ (fun x => P (c x)) ((K.comp D).comp
      ((cover.physicalNewSignProjection hδ hν χ hχ).comp (K.comp D).adjoint))=
      columnLinearTrace μ (fun x => A (cylinderAutomorphic (c x)))
        (completedNewSignSpace N hN.1 χ).starProjection := by
  intro S hS J K P D A
  rw [cover.physicalNewSignProjection_compact_energy hδ hν χ hχ R S hS.measurableSet μ c]
  unfold columnLinearTrace
  apply integral_congr_ae
  filter_upwards with x
  rw [adjoint_comp,Submodule.adjoint_subtypeL,comp_apply,
    compactQuotientRestriction_eq_boundedTransfer N hδ hν hR a b ha hheight]
  exact ((completedNewSignSpace N hN.1 χ).re_inner_starProjection_eq_normSq
    (A (cylinderAutomorphic (c x)))).symm

#print axioms physicalNewSignProjection_rectangle_trace
end QuantitativeMaass.AdmissibleScalarCover
