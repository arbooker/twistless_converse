module

public import QuantitativeEulerEndpointGoodSurvivorV1
public import AsymptoticFreshCompactDefectsV1
public import AsymptoticCongruenceTraceFiniteV1
public import QuantitativeSpectralFreshStepV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup AsymptoticObservationStack
open QuantitativeSpectralObservability
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hqN : ¬q∣N)
variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
variable (U : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)]

def freshSourceRows (x : ℍ) (i : Fin (q-1)) : Space →L[ℂ] Space :=
  (AsymptoticFreshCompactDefects.row N q hN hqN w hs hε t i x).comp (U x).starProjection

theorem fresh_source_rows_regular
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection)) (i : Fin (q-1)) :
    (∀ g h, Measurable (fun x => matrix (freshSourceRows N q hN hqN w hs hε t U x i) g h)) ∧
      Covariant (fun x => freshSourceRows N q hN hqN w hs hε t U x i) := by
  have hr := AsymptoticFreshCompactDefects.row_regular N q hN hqN w hs hε t i
  exact ⟨matrix_comp_measurable _ _ hr.1 hmU,covariant_comp _ _ hr.2 hcU⟩

theorem fresh_source_rows_supported
    (hU : ∀ x, Supported (integralGroup q) (U x).starProjection) (x : ℍ) (i : Fin (q-1)) :
    Supported (integralGroup q) (freshSourceRows N q hN hqN w hs hε t U x i) :=
  supported_comp _ _ _ (AsymptoticFreshCompactDefects.row_supported N q hN hqN w hs hε t i x) (hU x)

theorem fresh_source_rows_fixed (x : ℍ) (i : Fin (q-1)) :
    (freshSourceRows N q hN hqN w hs hε t U x i).comp (U x).starProjection=
      freshSourceRows N q hN hqN w hs hε t U x i := by
  unfold freshSourceRows
  rw [comp_assoc, show (U x).starProjection.comp (U x).starProjection = (U x).starProjection from
    (U x).isIdempotentElem_starProjection]

theorem fresh_source_rows_apply (x : ℍ) (i : Fin (q-1)) (v : Space) (hv : v∈U x) :
    freshSourceRows N q hN hqN w hs hε t U x i v=
      AsymptoticFreshCompactDefects.row N q hN hqN w hs hε t i x v := by
  simp only [freshSourceRows,comp_apply,(U x).starProjection_eq_self_iff.mpr hv]

theorem fresh_source_rows_norm (x : ℍ) (i : Fin (q-1)) :
    ‖freshSourceRows N q hN hqN w hs hε t U x i‖≤
      AsymptoticFreshCompactDefects.rowBound N q hN hqN w hs hε t i := by
  apply (opNorm_comp_le _ _).trans
  exact ((mul_le_mul_of_nonneg_left (U x).starProjection_norm_le (norm_nonneg _)).trans
    (by simpa only [mul_one] using
      AsymptoticFreshCompactDefects.row_norm_le N q hN hqN w hs hε t i x))

theorem fresh_source_stack_bounded : ∃ M : ℝ, ∀ x,
    ‖stack (freshSourceRows N q hN hqN w hs hε t U x)‖≤M := by
  exact ⟨_,fun x => stack_norm_le _ _
    (AsymptoticFreshCompactDefects.rowBound_nonneg N q hN hqN w hs hε t)
    (fresh_source_rows_norm N q hN hqN w hs hε t U x)⟩

omit [Fact q.Prime] in
 def sourceSampling (H : ℝ) (ht : 1≤t) (x : ℍ) : Space →L[ℂ] Space :=
  (fundamentalSampling N hN H hε ht x).comp (U x).starProjection

omit [Fact q.Prime] in
 theorem source_sampling_regular (H : ℝ) (ht : 1≤t)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection)) :
    (∀ g h, Measurable (fun x => matrix (sourceSampling N hN hε t U H ht x) g h)) ∧
      Covariant (sourceSampling N hN hε t U H ht) := by
  have hr := fundamentalSampling_regular N hN H hε ht
  exact ⟨matrix_comp_measurable _ _ hr.1 hmU,covariant_comp _ _ hr.2 hcU⟩

omit [Fact q.Prime] in
 theorem source_sampling_bounded (H : ℝ) (hH : 0≤H) (ht : 1≤t) :
    ∃ M : ℝ, ∀ x, ‖sourceSampling N hN hε t U H ht x‖≤M := by
  refine ⟨QuantitativeSpectralObservabilitySampling.samplingBound N hN H ε t*
    (8*QuantitativeSpectralCoverUnweight.coverBound N hN*(H+3)+5),fun x => (opNorm_comp_le _ _).trans ?_⟩
  exact ((mul_le_mul_of_nonneg_left (U x).starProjection_norm_le (norm_nonneg _)).trans
    (by simpa only [mul_one] using fundamentalSampling_norm N hN H hH hε ht x))

omit [Fact q.Prime] in
 theorem source_sampling_range (H : ℝ) (ht : 1≤t) (x : ℍ) (v : Space) :
    sourceSampling N hN hε t U H ht x v∈AsymptoticCongruenceQuotient.quotientSpace N hε ht x :=
  fundamentalSampling_range N hN H hε ht x _

#print axioms fresh_source_rows_regular
#print axioms fresh_source_rows_supported
#print axioms fresh_source_rows_fixed
#print axioms fresh_source_stack_bounded
#print axioms source_sampling_bounded
end QuantitativeEulerEndpointPrepared
