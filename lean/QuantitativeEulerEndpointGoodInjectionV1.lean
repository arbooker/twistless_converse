module

public import QuantitativeSpectralExceptionalGoodRootV1
public import AsymptoticRegularEmbeddingTraceV1
public import QuantitativeSpectralRegularCornerStepV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalGoodRoot (family source family_regular source_projection family_norm source_map source_trace)
open QuantitativeSpectralCornerCutRow
open AsymptoticRegularCompactBranch (Space)
open scoped InnerProduct

theorem trace_le_of_injective_map_good (N : ℕ) (hN : 0<N)
    (U V : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)] [∀ x, CompleteSpace (V x)]
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (B : ℍ → Space →L[ℂ] Space)
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (M : ℝ) (hM : ∀ x, ‖B x‖≤M)
    (hinj : ∀ x, fundamentalGood N x → ∀ v∈U x, B x v=0 → v=0)
    (hmap : ∀ x, fundamentalGood N x → ∀ v∈U x, B x v∈V x) :
    trace volume (fun x => (U x).starProjection)≤trace volume (fun x => (V x).starProjection) := by
  have hU := family_regular N hN (fun x => (U x).starProjection) hmU hcU
  have hB := family_regular N hN B hmB hcB
  have hmU' : ∀ g h, Measurable (fun x => matrix (source N U x).starProjection g h) := by
    simpa only [source_projection] using hU.1
  have hcU' : Covariant (fun x => (source N U x).starProjection) := by
    simpa only [source_projection] using hU.2
  have hi : ∀ x v, v∈source N U x → family N B x v=0 → v=0 := by
    intro x v hv hz
    by_cases hx : fundamentalGood N x
    · simp only [source,ite_eq_left hx] at hv
      simp only [family,ite_eq_left hx] at hz
      exact hinj x hx v hv hz
    · simpa only [source,ite_eq_right hx,Submodule.mem_bot] using hv
  have he := trace_le_of_injective_map volume AsymptoticRationalGroup.measurePreserving
    (source N U) (source N V) hmU' hcU' (family N B) hB.1 hB.2 M
    (family_norm N B hM) hi (source_map N U V B hmap)
  rw [source_trace N hN U,source_trace N hN V] at he
  exact he

/-- Energy on the actual compressed spectral survivor. No commutation
between the source projection and the observation is assumed. -/
theorem nextSpace_energy (U : Submodule ℂ Space) [CompleteSpace U]
    (T : Space →L[ℂ] Space) (c : ℝ) (v : Space) (hv : v∈nextSpace U T c) :
    ‖T v‖^2≤c^2*‖v‖^2 := by
  have hp : v∈U := nextSpace_le U T c hv
  have he : restricted U T v=T v := by
    change T (U.starProjection v)=T v
    rw [U.starProjection_eq_self_iff.mpr hp]
  have hl := QuantitativeSpectralCut.quadratic_le_on_lowAt _
    (IsSelfAdjoint.star_mul_self (restricted U T)) (c^2) (nextSpace_low U T c hv)
  change (inner ℂ (((restricted U T).adjoint.comp (restricted U T)) v) v).re≤_ at hl
  rw [comp_apply,adjoint_inner_left] at hl
  have hquad : (inner ℂ (restricted U T v) (restricted U T v)).re=‖restricted U T v‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (restricted U T v)).symm
  rwa [hquad,he] at hl

#print axioms trace_le_of_injective_map_good
#print axioms nextSpace_energy
end QuantitativeEulerEndpointPrepared
