module

public import QuantitativeSpectralObservabilitySamplingV1
public import AsymptoticOrbitDecodeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralObservabilityDecoded

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralObservability
open AsymptoticRegularBranchFamily AsymptoticFreshCompactDefects AsymptoticOrbitDecode
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped lp

attribute [local instance] Classical.propDecidable

/-- The actual periodic sampling operator: fold the input first, then
remove the cap. No unbounded full-orbit lift of a strip vector is used. -/
def sampling (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  (sampler N hN H hε t z).comp
    (compact identityBranch (wideCompactCover_compact N hN H) hε t z)

theorem sampling_decode (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (f : ℓ²(G,ℂ)) (g : G) :
    sampling N hN H hε t z f g =
      if g • z ∈ wideCompactCover N H then decode ε t z f g else 0 := by
  classical
  rw [sampling, comp_apply, sampler_apply, compact_decode, identityBranch_label, one_mul]
  by_cases hg : g • z ∈ wideCompactCover N H
  · rw [QuantitativeSpectralObservabilityUnweight.coefficient, Set.indicator_of_mem hg, ite_eq_left hg]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (AsymptoticCompactBranch.cap_pos hε t (g • z)).ne']
    simp [hg]
  · rw [QuantitativeSpectralObservabilityUnweight.coefficient, Set.indicator_of_notMem hg, ite_eq_right hg, zero_mul]
    simp only [ite_eq_right hg]

theorem sampling_regular (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) :
    (∀ g h : G, Measurable (fun z => matrix (sampling N hN H hε t z) g h)) ∧
      Covariant (sampling N hN H hε t) := by
  have hs := sampler_regular N hN H hε t
  exact ⟨matrix_comp_measurable _ _ hs.1
    (compact_matrix_measurable identityBranch (wideCompactCover_compact N hN H) hε t),
    covariant_comp _ _ hs.2 (compact_covariant identityBranch (wideCompactCover_compact N hN H) hε t)⟩

theorem sampling_norm (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) : ‖sampling N hN H hε t z‖ ≤
      samplingBound N hN H ε t * bound identityBranch (wideCompactCover_compact N hN H) hε t := by
  exact (opNorm_comp_le _ _).trans (mul_le_mul (sampler_norm N hN H hε t z)
    (compact_norm_le identityBranch (wideCompactCover_compact N hN H) hε t z)
    (norm_nonneg _) (samplingBound_nonneg N hN H ε t))

theorem sampling_fresh_supported (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (q : ℕ) [Fact q.Prime] :
    Supported (integralGroup q) (sampling N hN H hε t z) := by
  apply supported_comp _ _ _ (sampler_supported N hN H hε t z _)
  apply compact_operator_supported_of_label
  rw [identityBranch_label]
  exact (integralGroup q).one_mem

#print axioms sampling_decode
#print axioms sampling_regular
#print axioms sampling_fresh_supported

end QuantitativeSpectralObservabilityDecoded
