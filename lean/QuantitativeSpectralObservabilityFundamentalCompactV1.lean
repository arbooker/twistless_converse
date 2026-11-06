module

public import QuantitativeSpectralObservabilityFundamentalV1
public import QuantitativeSpectralObservabilitySamplerNormV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilityDecoded QuantitativeSpectralObservabilitySampling
open QuantitativeSpectralCoverUnweight
open scoped Modular lp ENNReal

attribute [local instance] Classical.propDecidable

theorem fundamentalCompact_compact (N : ℕ) (hN : 0<N) (H : ℝ) :
    IsCompact (fundamentalCompact N H) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hc : IsCompact (𝒟 ∩ {z : ℍ | z.im≤H}) :=
    (wideBox_compact H).of_isClosed_subset
      (ModularGroup.isClosed_fd.inter (isClosed_le continuous_im continuous_const))
      (fun _ hz => modular_fd_subset_wideBox hz.1 hz.2)
  apply isCompact_iUnion
  intro q
  exact hc.image (AsymptoticRationalBranches.action_continuous _)

theorem fundamentalCompact_subset (N : ℕ) (H : ℝ) :
    fundamentalCompact N H ⊆ fundamentalSet N := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨q,w,hw.1,rfl⟩

/-- Actual decoded sampling, with one fundamental-domain output
coordinate per congruence fibre outside the invariant boundary null set. -/
def fundamentalRawSampling (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (corner (fundamentalCompact N H) x).comp (sampling N hN H hε t x)

theorem fundamentalRawSampling_decode (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (g : AsymptoticRationalGroup.Group) :
    fundamentalRawSampling N hN H hε t x v g=
      if g • x∈fundamentalCompact N H then AsymptoticOrbitDecode.decode ε t x v g else 0 := by
  classical
  rw [fundamentalRawSampling,comp_apply,corner_apply]
  by_cases hg : g • x∈fundamentalCompact N H
  · rw [ite_eq_left hg,sampling_decode,ite_eq_left (fundamentalCompact_subset_wide N H hg),
      ite_eq_left hg]
  · rw [ite_eq_right hg,ite_eq_right hg]

theorem fundamentalRawSampling_norm (N : ℕ) (hN : 0<N) (H : ℝ) (hH : 0≤H)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖fundamentalRawSampling N hN H hε t x‖≤
      samplingBound N hN H ε t*(8*coverBound N hN*(H+3)+5) := by
  apply (opNorm_comp_le _ _).trans
  exact ((mul_le_mul_of_nonneg_right (AsymptoticOrbitRegion.corner_norm_le _ _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using sampling_polynomial_norm N hN H hH hε t x))

theorem fundamentalRawSampling_regular (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) :
    (∀ g h, Measurable (fun x => matrix (fundamentalRawSampling N hN H hε t x) g h)) ∧
      Covariant (fundamentalRawSampling N hN H hε t) := by
  have hs := sampling_regular N hN H hε t
  exact ⟨matrix_comp_measurable _ _
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      (fundamentalCompact_compact N hN H).measurableSet) hs.1,
    covariant_comp _ _ (corner_covariant _) hs.2⟩

theorem fundamentalRawSampling_supported (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (corner (fundamentalSet N) x).comp (fundamentalRawSampling N hN H hε t x)=
      fundamentalRawSampling N hN H hε t x := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  rw [comp_apply,corner_apply,fundamentalRawSampling_decode]
  by_cases hg : g • x∈fundamentalCompact N H
  · rw [ite_eq_left (fundamentalCompact_subset N H hg)]
  · simp only [ite_eq_right hg,ite_self]

#print axioms fundamentalRawSampling_decode
#print axioms fundamentalRawSampling_norm
#print axioms fundamentalRawSampling_regular

end QuantitativeSpectralObservability
