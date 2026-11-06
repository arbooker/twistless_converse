module

public import QuantitativeSpectralExceptionalRetainedFactorV1
public import QuantitativeSpectralObservabilityFundamentalCompactV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily
open AsymptoticCongruenceLabels AsymptoticOrbitDiagonal AsymptoticObservationStack
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open scoped MatrixGroups lp

variable {ι : Type*} [Fintype ι]

/-- The rational row evaluated at its reducing labels using the literal
fundamental-domain raw sampler. -/
def fundamentalReducedFamily (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  ∑ i, c i • (pull (integralLabel (γ i)*label (b i))).comp
    (fundamentalRawSampling N hN H hε t x)

/-- At genuinely reduced coordinates, the literal FD sampler returns the
same decoded value as the wide sampler. This is a coordinate computation. -/
theorem fundamentalReducedFamily_eq (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ) (E : Set ℍ)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i)*label (b i)) • z ∈ fundamentalCompact N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    (corner E x).comp (fundamentalReducedFamily N hN H b γ c hε t x) =
      (corner E x).comp (reducedFamily N hN H b γ c hε t x) := by
  simp only [fundamentalReducedFamily,reducedFamily,comp_finsetSum,comp_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp only [comp_apply,corner_apply]
  by_cases hg : g • x ∈ E
  · have hh : ((integralLabel (γ i)*label (b i))*g) • x ∈ fundamentalCompact N H := by
      rw [mul_smul]
      exact hred i _ hg
    rw [ite_eq_left hg,ite_eq_left hg,pull_apply,pull_apply,
      fundamentalRawSampling_decode,sampling_decode,ite_eq_left hh,
      ite_eq_left (fundamentalCompact_subset_wide N H hh)]
  · simp only [ite_eq_right hg]

theorem fundamental_retained_identity (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i)*label (b i)) • z ∈ fundamentalCompact N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (corner E x).comp (fundamentalReducedFamily N hN H b γ c hε t x) =
      (corner E x).comp
        ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (family b c hs hε t x) +
          correctionFamily b γ c hs hε t Db x) := by
  rw [fundamentalReducedFamily_eq N hN H b γ c E hred hε t x]
  exact retained_family_identity N hN H b γ c hs hEs
    (fun i z hz => fundamentalCompact_subset_wide N H (hred i z hz)) hε t Ds Db x

#print axioms fundamental_retained_identity

end QuantitativeSpectralExceptionalReducedRows
