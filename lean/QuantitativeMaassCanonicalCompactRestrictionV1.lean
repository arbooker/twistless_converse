module

public import QuantitativeMaassCanonicalMetricTraceV1
public import QuantitativeMaassCompactQuotientRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCompactBranch

namespace QuantitativeMaass.AdmissibleScalarCover

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- The exact canonical term after compact input localization is the
column energy of the actual compact quotient restriction. The metric
cancels and no inverse-Gram polynomial or packet intertwining is used.
The preceding representative theorem identifies this restriction as
unweighted when the region lies above the propagated lower cutoff. -/
theorem physicalNewSignProjection_compact_energy
    {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (R : ℝ) (S : Set ℍ) (hS : MeasurableSet S)
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : α → Lp ℂ 2 (quotientMeasure 0)) :
    let J := ⌈(ν : ℝ) * R + 1⌉₊
    let K := ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
      LogBands.inverse (quotientMeasure 0)
        (fun z => Real.log (cappedHeightWeight δ ν z))
        (Real.measurable_log.comp (cap_continuous δ ν).measurable) n
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS
    let D := (cover.metric hδ hν).change.symm.toContinuousLinearMap
    let V := (compactQuotientRestriction N hδ hν R S hS).comp
      (completedNewSignSpace N hN.1 χ).subtypeL
    columnLinearTrace μ (fun x => P (c x)) ((K.comp D).comp
      ((cover.physicalNewSignProjection hδ hν χ hχ).comp (K.comp D).adjoint)) =
      ∫ x, ‖V.adjoint (c x)‖ ^ 2 ∂μ := by
  intro J K P D V
  rw [cover.physicalNewSignProjection_column_energy hδ hν χ hχ μ (fun x => P (c x)) K]
  let W := completedNewSignWeightedEmbedding N hN.1 hδ hν χ
  have hV : V = P.comp (K.comp W) := by
    rfl
  rw [hV]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [adjoint_comp, comp_apply]
  rw [show P.adjoint = P from AsymptoticRegionL2.projection_adjoint (quotientMeasure 0) S hS]

#print axioms physicalNewSignProjection_compact_energy

end QuantitativeMaass.AdmissibleScalarCover
