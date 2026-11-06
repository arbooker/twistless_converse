module

public import QuantitativeSpectralExceptionalWideV1
public import QuantitativeSpectralObservabilityDecodedV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalWideSampling

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticObservationStack QuantitativeSpectralExceptionalWide
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open scoped lp ENNReal

variable {ι : Type*}

/-- The literal fixed local rows after the wide decoded sampling map. -/
def sampled (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (L : ℍ → ι → Space →L[ℂ] Space) (x : ℍ) (i : ι) : Space →L[ℂ] Space :=
  (L x i).comp (sampling N hN H hε t x)

/-- Exact retained/exceptional factorization with the actual wide sampler. -/
theorem sampled_factorization (N : ℕ) (hN : 0 < N) (H C : ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (L : ℍ → ι → Space →L[ℂ] Space) (x : ℍ) (i : ι) :
    (L x i).comp (sampling N hN H hε t x) =
      interior N H C (sampled N hN H hε t L) x i +
        boundary N H C (sampled N hN H hε t L) x i :=
  row_factorization N H C (sampled N hN H hε t L) x i

theorem sampled_regular (N : ℕ) (hN : 0 < N) (H : ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (L : ℍ → ι → Space →L[ℂ] Space)
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i)) (i : ι) :
    (∀ g h, Measurable (fun x => matrix (sampled N hN H hε t L x i) g h)) ∧
      Covariant (fun x => sampled N hN H hε t L x i) := by
  have hs := sampling_regular N hN H hε t
  exact ⟨matrix_comp_measurable _ _ (hm i) hs.1, covariant_comp _ _ (hc i) hs.2⟩

/-- The actual exceptional map after wide sampling has O(1/H) polar
rank, with no sampling norm in the explicit rank constant. -/
theorem sampled_boundary_rank [Fintype ι] (N : ℕ) (hN : 0 < N)
    {H C : ℝ} (hH : 0 < H) (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (L : ℍ → ι → Space →L[ℂ] Space)
    (hm : ∀ i g h, Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i, Covariant (fun x => L x i))
    (M : ι → ℝ) (hM0 : ∀ i, 0 ≤ M i) (hM : ∀ x i, ‖L x i‖ ≤ M i) :
    trace volume (fun x =>
      (stack (boundary N H C (sampled N hN H hε t L) x)).kerᗮ.starProjection) ≤
      (Fintype.card ι : ℝ≥0∞) *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N) : ℝ≥0∞) *
          (3 * ENNReal.ofReal (C/H)) := by
  let K := QuantitativeSpectralObservabilitySampling.samplingBound N hN H ε t *
    AsymptoticRegularBranchFamily.bound AsymptoticFreshCompactDefects.identityBranch
      (wideCompactCover_compact N hN H) hε t
  have hK : 0 ≤ K := mul_nonneg
    (QuantitativeSpectralObservabilitySampling.samplingBound_nonneg N hN H ε t)
    (AsymptoticRegularBranchFamily.bound_nonneg _ _ _ _)
  have hr := sampled_regular N hN H hε t L hm hc
  apply boundary_stack_rank N hN hH hC (sampled N hN H hε t L)
    (fun i => (hr i).1) (fun i => (hr i).2)
    (fun i => M i*K) (fun i => mul_nonneg (hM0 i) hK)
  intro x i
  exact (opNorm_comp_le _ _).trans (mul_le_mul (hM x i)
    (sampling_norm N hN H hε t x) (norm_nonneg _) (hM0 i))

#print axioms sampled_factorization
#print axioms sampled_regular
#print axioms sampled_boundary_rank

end QuantitativeSpectralExceptionalWideSampling
