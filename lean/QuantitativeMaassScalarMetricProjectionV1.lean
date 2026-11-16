module

public import QuantitativeMaassScalarMetricPacketV1
public import QuantitativeMaassMetricExcessPullbackV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticClassicalPetersson MeasureTheory
namespace QuantitativeMaass

/-- Cogram formula for an actual isometric embedding onto its closed range. -/
theorem isometric_cogram_projection {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : V→ₗᵢ[ℂ]H) [J.toContinuousLinearMap.range.HasOrthogonalProjection] :
    J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint=
      J.toContinuousLinearMap.range.starProjection := by
  let R := J.toContinuousLinearMap
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨R.adjoint x,rfl⟩
  · intro y hy
    obtain ⟨z,rfl⟩ := hy
    change inner ℂ (x-R (R.adjoint x)) (R z)=0
    rw [←R.adjoint_inner_left,map_sub]
    have he := congrArg (fun T : V→L[ℂ]V => T (R.adjoint x)) J.adjoint_comp_self
    change R.adjoint (R (R.adjoint x))=R.adjoint x at he
    rw [he,sub_self,inner_zero_left]

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- Actual scalar-metric target projection; defined as its isometric cogram. -/
def scalarMetricNewSignProjection (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  (scalarMetricNewSignIsometry N hN hδ hν χ hχ).toContinuousLinearMap.comp
    (scalarMetricNewSignIsometry N hN hδ hν χ hχ).toContinuousLinearMap.adjoint

theorem scalarMetricNewSignProjection_isProjection (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    IsSelfAdjoint (scalarMetricNewSignProjection N hN hδ hν χ hχ) ∧
    (scalarMetricNewSignProjection N hN hδ hν χ hχ).comp
      (scalarMetricNewSignProjection N hN hδ hν χ hχ)=
        scalarMetricNewSignProjection N hN hδ hν χ hχ := by
  let J := (scalarMetricNewSignIsometry N hN hδ hν χ hχ).toContinuousLinearMap
  have hg : J.adjoint.comp J=1 := scalarMetricNewSignIsometry_gram N hN hδ hν χ hχ
  constructor
  · change IsSelfAdjoint (J.comp J.adjoint)
    change (J.comp J.adjoint).adjoint=J.comp J.adjoint
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  · change (J.comp J.adjoint).comp (J.comp J.adjoint)=J.comp J.adjoint
    calc
      _ = J.comp ((J.adjoint.comp J).comp J.adjoint) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hg]; rfl

/-- Pullback of the actual canonical projection is the original weighted
new/sign cogram. In particular, there is no spectral inverse Gram here. -/
theorem scalarMetricNewSignProjection_pullback (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    let D := (admissibleScalarMetric N hN hδ hν).change.symm.toContinuousLinearMap
    (D.comp (scalarMetricNewSignProjection N hN hδ hν χ hχ)).comp D.adjoint=
      (completedNewSignWeightedEmbedding N hN.1 hδ hν χ).comp
        (completedNewSignWeightedEmbedding N hN.1 hδ hν χ).adjoint := by
  exact metric_cogram_pullback (admissibleScalarMetric N hN hδ hν).change
    (completedNewSignWeightedEmbedding N hN.1 hδ hν χ)

#print axioms isometric_cogram_projection
#print axioms scalarMetricNewSignProjection_isProjection
#print axioms scalarMetricNewSignProjection_pullback
end QuantitativeMaass
