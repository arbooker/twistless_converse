module

public import QuantitativeSpectralObservabilityOldTailStackV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticObservationStack AsymptoticPolarIsometry AsymptoticCornerKernel
open scoped lp ENNReal

/-- Removing a bounded regular error from any regular source costs at
most its full input support rank. Extended traces are allowed. -/
theorem source_trace_le_remaining_add_rank
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection))
    (T : ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x, ‖T x‖≤M) :
    trace volume (fun x => (P x).starProjection)≤
      trace volume (fun x => (remaining (P x) (T x)).starProjection)+
        trace volume (fun x => (T x).kerᗮ.starProjection) := by
  have hr := source_support_regular (fun x => (T x).comp (P x).starProjection)
    (matrix_comp_measurable _ _ hm hmP) (covariant_comp _ _ hc hcP) M
    (fun x => (restricted_norm_le (P x) (T x)).trans (hM x))
  have he := corner_trace_add volume P (fun x => (T x).comp (P x).starProjection)
    (fun x => restricted_comp_projection (P x) (T x)) (hr.1 1 1)
  simp only [remaining_restricted] at he
  have hi (x : ℍ) : outputSpace ((T x).comp (P x).starProjection)≤outputSpace (T x) := by
    apply Submodule.topologicalClosure_mono
    rintro _ ⟨v,rfl⟩
    exact ⟨(P x).starProjection v,rfl⟩
  have hmono := projection_trace_mono volume _ _ hi
  rw [← support_trace_eq volume AsymptoticRationalGroup.measurePreserving
    (fun x => (T x).comp (P x).starProjection)
    (matrix_comp_measurable _ _ hm hmP) (covariant_comp _ _ hc hcP) M
    (fun x => (restricted_norm_le (P x) (T x)).trans (hM x)),
    ← support_trace_eq volume AsymptoticRationalGroup.measurePreserving T hm hc M hM] at hmono
  exact he.le.trans (add_le_add le_rfl hmono)

/-- A simultaneous surviving source for all old rows: every tail error
vanishes there, and the trace loss is bounded by the explicit sum of
geometric tail areas. No invariance or small-residual premise is assumed. -/
theorem oldTailStack_survivor_trace {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    {Y : ℝ} (hY : 0≤Y) (H : I → ℝ) (hH : ∀ i, 0<H i)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    trace volume (fun x => (P x).starProjection)≤
      trace volume (fun x => (remaining (P x) (oldTailStack N hN J hJ Y H hε ht x)).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨M,_hM,hbound,hm,hc⟩ := oldTailStack_absolute_regular N hN J hJ hY H hε ht
  have he := source_trace_le_remaining_add_rank P hmP hcP
    (fun x => absolute (oldTailStack N hN J hJ Y H hε ht x)) hm hc M hbound
  simp only [remaining,absolute_ker] at he
  exact he.trans (add_le_add le_rfl (oldTailStack_source_rank N hN J hJ hY H hH hε ht))

theorem oldTailStack_survivor_regular {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (J : I → Subgroup OrbitGroup)
    (hJ : ∀ i, gamma N≤J i) [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
    {Y : ℝ} (hY : 0≤Y) (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (P : ℍ → Submodule ℂ ℓ²(OrbitGroup,ℂ)) [∀ x, CompleteSpace (P x)]
    (hmP : ∀ g h, Measurable (fun x => matrix (P x).starProjection g h))
    (hcP : Covariant (fun x => (P x).starProjection)) :
    (∀ g h, Measurable (fun x => matrix
      (remaining (P x) (oldTailStack N hN J hJ Y H hε ht x)).starProjection g h)) ∧
    Covariant (fun x => (remaining (P x) (oldTailStack N hN J hJ Y H hε ht x)).starProjection) := by
  obtain ⟨M,_hM,hbound,hm,hc⟩ := oldTailStack_absolute_regular N hN J hJ hY H hε ht
  have he := remaining_regular P hmP hcP
    (fun x => absolute (oldTailStack N hN J hJ Y H hε ht x)) hm hc M hbound
  simpa only [remaining,absolute_ker] using he

#print axioms source_trace_le_remaining_add_rank
#print axioms oldTailStack_survivor_trace
#print axioms oldTailStack_survivor_regular

end QuantitativeSpectralObservability
