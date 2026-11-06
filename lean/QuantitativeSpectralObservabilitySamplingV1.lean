module

public import QuantitativeSpectralObservabilityUnweightV1
public import AsymptoticSubgroupSupportV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralObservabilitySampling

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticOrbitDiagonal AsymptoticCompactBranch AsymptoticSubgroupSupport
open QuantitativeSpectralObservabilityUnweight QuantitativeSpectralObservability
open QuantitativeSpectralCoverUnweight (coverBound)
open scoped lp

attribute [local instance] Classical.propDecidable

abbrev G := AsymptoticRationalGroup.Group

def samplingBound (N : ℕ) (hN : 0 < N) (H ε : ℝ) (t : ℕ) : ℝ :=
  (max 1 (4*ε*(coverBound N hN)^2*(H+3)^2))^t

theorem samplingBound_nonneg (N : ℕ) (hN : 0 < N) (H ε : ℝ) (t : ℕ) :
    0 ≤ samplingBound N hN H ε t := by unfold samplingBound; positivity

/-- Literal compactly truncated unweighting on every regular orbit. Its
norm cost is polynomial in the cusp cutoff, with fixed level constants. -/
def sampler (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  operator (fun g => coefficient N H ε t (g • z))
    (samplingBound_nonneg N hN H ε t) (fun g => coefficient_norm_le N hN H hε t (g • z))

theorem sampler_apply (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (f : ℓ²(G,ℂ)) (g : G) :
    sampler N hN H hε t z f g = coefficient N H ε t (g • z)*f g := rfl

theorem sampler_norm (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) : ‖sampler N hN H hε t z‖ ≤ samplingBound N hN H ε t :=
  operator_norm_le _ _ _

theorem sampler_matrix (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (g h : G) :
    matrix (sampler N hN H hε t z) g h =
      if g=h then coefficient N H ε t (g • z) else 0 :=
  by
    classical
    by_cases he : g=h
    · subst h
      simp [matrix, sampler_apply, delta]
    · simp [matrix, sampler_apply, delta, he]

theorem sampler_regular (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) :
    (∀ g h : G, Measurable (fun z => matrix (sampler N hN H hε t z) g h)) ∧
      Covariant (sampler N hN H hε t) := by
  constructor
  · intro g h
    simp only [sampler_matrix]
    by_cases he : g=h
    · simp only [he, ite_true]
      exact (coefficient_measurable N hN H ε t).comp
        (AsymptoticRationalGroup.measurePreserving h).measurable
    · simp only [he, ite_false]
      exact measurable_const
  · intro z a g h
    simp only [sampler_matrix, mul_right_cancel_iff, mul_smul]

/-- Observation cutoffs and unweighting never introduce a fresh prime
in a branch: this actual operator is supported in every subgroup. -/
theorem sampler_supported (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (S : Subgroup G) : Supported S (sampler N hN H hε t z) := by
  classical
  intro g h hgh
  have he : g ≠ h := by intro he; subst h; exact hgh (by simp)
  simp only [sampler_matrix, he, ite_false]

/-- Exact cancellation of the original cap on the retained set. This
identity concerns the actual orbit coordinates, not a replacement weight. -/
theorem sampler_weight_cancel (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (z : ℍ) (f v : ℓ²(G,ℂ))
    (hv : ∀ g : G, v g = Complex.ofReal (cap ε t (g • z))*f g) :
    sampler N hN H hε t z v = corner (wideCompactCover N H) z f := by
  classical
  apply lp.ext
  funext g
  rw [sampler_apply, corner_apply, hv g]
  by_cases hg : g • z ∈ wideCompactCover N H
  · rw [QuantitativeSpectralObservabilityUnweight.coefficient, Set.indicator_of_mem hg, ite_eq_left hg]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (cap_pos hε t (g • z)).ne']
    simp
  · rw [QuantitativeSpectralObservabilityUnweight.coefficient, Set.indicator_of_notMem hg, ite_eq_right hg, zero_mul]

#print axioms sampler_regular
#print axioms sampler_supported
#print axioms sampler_weight_cancel

end QuantitativeSpectralObservabilitySampling
