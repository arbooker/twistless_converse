module

public import QuantitativeMaassCompactCapRestrictionV1
public import QuantitativeMaassWeightedQuotientEmbeddingV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticCompactBranch

namespace QuantitativeMaass

theorem compact_cap_log_measurable (δ : ℝ) (v : ℕ) :
    Measurable (fun z : ℍ => Real.log (cappedHeightWeight δ v z)) :=
  Real.measurable_log.comp (cap_continuous δ v).measurable

/-- Bounded realization of unweighted quotient restriction on regions
above the propagated lower cutoff. The inverse cap uses only finitely
many logarithmic bands. -/
def compactQuotientRestriction (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {v : ℕ} (hv : 1 ≤ v) (R : ℝ) (S : Set ℍ) (hS : MeasurableSet S) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  let J := ⌈(v : ℝ) * R + 1⌉₊
  let K := ∑ n ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
    LogBands.inverse (quotientMeasure 0)
      (fun z => Real.log (cappedHeightWeight δ v z)) (compact_cap_log_measurable δ v) n
  (AsymptoticRegionL2.projection (quotientMeasure 0) S hS).comp
    (K.comp (weightedQuotientEmbedding N hδ hv))

/-- The bounded operator is the literal unweighted restriction on the
dense automorphic representatives, not a substituted packet or model. -/
theorem compactQuotientRestriction_representative (N : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : ℕ} (hv : 1 ≤ v)
    {R : ℝ} (hR : 0 ≤ R) (S : Set ℍ) (hS : MeasurableSet S)
    (hheight : ∀ z ∈ S, δ * Real.exp (-R) ≤ z.im)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    compactQuotientRestriction N hδ hv R S hS
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)
      =ᵐ[quotientMeasure 0] S.indicator f.val := by
  have hf : weightedQuotientEmbedding N hδ hv
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)
      =ᵐ[quotientMeasure 0] (fun z => (cappedHeightWeight δ v z : ℂ) * f.val z) := by
    rw [weightedQuotientEmbedding_representative]
    exact MemLp.coeFn_toLp (weightedRepresentative_memLp N hδ hv f)
  exact compact_inverse_cap_restriction_coeFn (quotientMeasure 0) hδ hR v
    (compact_cap_log_measurable δ v) S hS hheight _ f.val hf

/-- The local unweighted function is square-integrable on the cylinder,
as a consequence of the actual quotient embedding and cap cancellation. -/
theorem compactQuotientRepresentative_memLp (N : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : ℕ} (hv : 1 ≤ v)
    {R : ℝ} (hR : 0 ≤ R) (S : Set ℍ) (hS : MeasurableSet S)
    (hheight : ∀ z ∈ S, δ * Real.exp (-R) ≤ z.im)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    MemLp (S.indicator f.val) 2 (quotientMeasure 0) :=
  (memLp_congr_ae (compactQuotientRestriction_representative N hδ hv hR S hS hheight f)).mp
    (Lp.memLp _)

#print axioms compactQuotientRestriction_representative
#print axioms compactQuotientRepresentative_memLp

end QuantitativeMaass
