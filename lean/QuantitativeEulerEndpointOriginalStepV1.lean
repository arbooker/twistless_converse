module

public import QuantitativeEulerEndpointFreshTraceV1
public import AsymptoticFreshEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticObservationStack
open AsymptoticMixing AsymptoticRegularObservationRows
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hqN : ¬q∣N)
variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
variable (U : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)]

/-- Exact normalized original twist after the source projection. -/
def normalizedSourceTwist (x : ℍ) : Space →L[ℂ] Space :=
  -(((Real.sqrt ((q-1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) •
    ((twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp (U x).starProjection)

theorem fresh_source_mixed_eq_original (x : ℍ) :
    normalizedMixed (primeLabels q) (freshSourceRows N q hN hqN w hs hε t U x)=
      normalizedSourceTwist N q hN w hs hε t U x := by
  have he : mixed (primeLabels q) (freshSourceRows N q hN hqN w hs hε t U x)=
      (mixed (primeLabels q) (fun i => AsymptoticFreshCompactDefects.row N q hN hqN w hs hε t i x)).comp
        (U x).starProjection := by
    simp only [mixed,freshSourceRows,finsetSum_comp,comp_assoc]
  rw [normalizedMixed_formula,he,AsymptoticFreshEquation.averaged_eq_negative_twist,neg_comp]
  simp only [normalizedSourceTwist,Fintype.card_fin,smul_neg,_root_.neg_smul]

theorem fresh_step_source_eq_original (d : ℝ) (x : ℍ) :
    freshStepSource N q hN hqN w hs hε t U d x=
      nextSpace (U x) (normalizedSourceTwist N q hN w hs hε t U x) d := by
  unfold freshStepSource
  rw [fresh_source_mixed_eq_original]

theorem fresh_step_source_regular
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection)) (d : ℝ) (hd : 0<d) :
    (∀ g h, Measurable (fun x => matrix (freshStepSource N q hN hqN w hs hε t U d x).starProjection g h)) ∧
      Covariant (fun x => (freshStepSource N q hN hqN w hs hε t U d x).starProjection) := by
  have hr := fresh_source_rows_regular N q hN hqN w hs hε t U hmU hcU
  have hm := normalizedMixed_regular (primeLabels q) _ (fun i => (hr i).1) (fun i => (hr i).2)
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q hN hqN w hs hε t U
  exact (step_regular U _ hmU hcU hm.1 hm.2 M
    (fun x => (normalizedMixed_norm _ _).trans (hM x)) d hd).1

/-- At every subsequent prime avoiding N and q the actual updated
source remains in the required integral subgroup algebra. -/
theorem fresh_step_source_supported (r : ℕ) [Fact r.Prime]
    (hrN : ¬r∣N) (hrq : ¬r∣q)
    (hU : ∀ x, Supported (integralGroup r) (U x).starProjection)
    (d : ℝ) (hd : 0<d) (x : ℍ) :
    Supported (integralGroup r) (freshStepSource N q hN hqN w hs hε t U d x).starProjection := by
  rw [AsymptoticPolarIsometry.starProjection_congr _ _
    (fresh_step_source_eq_original N q hN hqN w hs hε t U d x)]
  apply (step_supported _ _ _ (hU x) _ d hd).1
  apply supported_smul
  apply supported_comp _ _ _ _ (hU x)
  exact compact_family_supported r _ _
    (twistBranches_integral r N q hN (Fact.out : q.Prime).pos hrN hrq) hs hε t x

theorem fresh_step_source_le (d : ℝ) (x : ℍ) :
    freshStepSource N q hN hqN w hs hε t U d x≤U x := nextSpace_le _ _ _

theorem fresh_step_source_trace_finite
    (hf : trace volume (fun x => (U x).starProjection)<∞) (d : ℝ) :
    trace volume (fun x => (freshStepSource N q hN hqN w hs hε t U d x).starProjection)<∞ :=
  projection_trace_finite_of_le volume _ U (fresh_step_source_le N q hN hqN w hs hε t U d) hf

#print axioms fresh_source_mixed_eq_original
#print axioms fresh_step_source_regular
#print axioms fresh_step_source_supported
#print axioms fresh_step_source_trace_finite
end QuantitativeEulerEndpointPrepared
