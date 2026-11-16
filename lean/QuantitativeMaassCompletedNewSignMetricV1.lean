module

public import QuantitativeMaassCompletedNewSignSpaceV1
public import QuantitativeMaassTargetMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- A lower bounded embedding supplies an ambient normalization of its
closed range, with no chosen coordinates in the source. -/
theorem exists_targetMetric_of_lower_bound {H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (R : V →L[ℂ] H) {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    ∃ L : H ≃L[ℂ] H,∀ x,‖L (R x)‖=‖x‖ := by
  have hr := lower_energy_injective_closed (H := V) (K := H) R ha hR
  let W : Submodule ℂ H := R.range
  let : CompleteSpace W := hr.2.completeSpace_coe
  let J : V ≃L[ℂ] W := ContinuousLinearMap.equivRange (f := R) hr.1 hr.2
  have hJ (x : V) : a*‖x‖^2≤‖J x‖^2 := hR x
  refine ⟨targetMetric (H := H) (V := V) W J ha hJ,?_⟩
  intro x
  exact targetMetric_norm (H := H) (V := V) W J ha hJ x

/-- The concrete admissible new/sign target admits an ambient metric
change restoring its canonical quotient norm exactly. -/
theorem exists_completedNewSignMetric (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    ∃ L : Lp ℂ 2 (quotientMeasure 0) ≃L[ℂ] Lp ℂ 2 (quotientMeasure 0),
      ∀ x : completedNewSignSpace N hN.1 χ,
        ‖L (completedNewSignWeightedEmbedding N hN.1 hε hv χ x)‖=‖x‖ := by
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN hε hv
  apply exists_targetMetric_of_lower_bound
    (H := Lp ℂ 2 (quotientMeasure 0)) (V := completedNewSignSpace N hN.1 χ)
    (completedNewSignWeightedEmbedding N hN.1 hε hv χ) ha
  intro x
  exact hl χ hχ x

#print axioms exists_targetMetric_of_lower_bound
#print axioms exists_completedNewSignMetric

end QuantitativeMaass
