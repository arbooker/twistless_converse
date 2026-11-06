module

public import QuantitativeHolomorphicRegularSourceV1
public import QuantitativeHolomorphicRegularTraceComparisonV1
public import AsymptoticRegularSandwichBoundV1
public import AsymptoticRegularRetainedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

theorem observationRegularFilter_eq_source_sandwich (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (z : UpperHalfPlane) :
    observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d =
    (normalizedRegularAmbientCountReconstruction A hN P e z).comp
      ((regularSourceFilter A hN P e qs r s hs d z).comp
        (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint) := by
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S = 1 :=
    AsymptoticOrbitRegion.adjoint_comp_subtype (G := AsymptoticRationalGroup.Group)
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
  exact (finiteRowFilter_source_transport S hS
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) qs _ _ d).symm

/-- Exact cyclic transfer to the finite terminal source. In particular the
ambient complement introduced by a polynomial filter contributes no trace. -/
theorem observationRegularFilter_trace_eq_source (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    signedTrace volume (fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d) =
    signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  have hI := regularSourceFilter_regular A hN P e qs r s hs d
  have hf : AsymptoticRegularTrace.trace volume (fun z =>
      (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint.comp
        (normalizedRegularAmbientCountReconstruction A hN P e z)) < ∞ := by
    rw [normalizedRegularAmbientCountReconstruction_trace_gram]
    exact ENNReal.ofReal_lt_top
  have ht := signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving
    (normalizedRegularAmbientCountReconstruction A hN P e)
    (regularSourceFilter A hN P e qs r s hs d) hU.1 hI.1 hU.2 hI.2 hf
    (regularSourceFilter_norm_le A hN P e qs r s hs d)
  simpa only [← observationRegularFilter_eq_source_sandwich,
    normalizedRegularAmbientCountReconstruction_gram] using ht

theorem regularSourceFilter_positive (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (z : UpperHalfPlane) :
    (regularSourceFilter A hN P e qs r s hs d z).IsPositive := by
  apply nonneg_iff_isPositive.mp
  exact (finiteRowFilter_order qs _ _
    (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) _
    (normalizedRegularAmbientCountReconstruction_norm_le A hN P e z) d).1

theorem observationRegularFilter_positive (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (z : UpperHalfPlane) :
    (observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d).IsPositive := by
  rw [observationRegularFilter_eq_source_sandwich]
  simpa only [adjoint_adjoint,comp_assoc] using
    (regularSourceFilter_positive A hN P e qs r s hs d z).adjoint_conj
      (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint

theorem observationRegularFilter_trace_finite (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    AsymptoticRegularTrace.trace volume (fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d) < ∞ := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  have he := rational_trace_adjoint_mul (normalizedRegularAmbientCountReconstruction A hN P e)
    hU.1 hU.2
  have ht := trace_sandwich_le_range_gram volume
    (normalizedRegularAmbientCountReconstruction A hN P e)
    (regularSourceFilter A hN P e qs r s hs d)
    (regularSourceFilter_norm_le A hN P e qs r s hs d)
  simp only [← observationRegularFilter_eq_source_sandwich] at ht
  apply ht.trans_lt
  rw [← he,normalizedRegularAmbientCountReconstruction_trace_gram]
  exact ENNReal.ofReal_lt_top

/-- Removing both spatial cutoffs from the exact positive regular filter
only increases its trace, which then transfers exactly to the terminal source. -/
theorem observationRegularFilter_retained_trace_le_source (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (Y H : ℝ) :
    signedTrace volume (regularRetained Y H (fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d)) ≤
    signedTrace volume (fun z => (regularSourceFilter A hN P e qs r s hs d z).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)) := by
  let B := fun z => observationRegularFilter A hN P e qs r s hs z
    (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
  have hm := (observationRegularFilter_regular A hN P e qs r s hs d).1
  have hp := observationRegularFilter_positive A hN P e qs r s hs d
  have hpr (z : UpperHalfPlane) : (regularRetained Y H B z).IsPositive := by
    simpa only [regularRetained,AsymptoticOrbitDiagonal.corner_adjoint,comp_assoc] using
      (hp z).adjoint_conj (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)
  have htr : AsymptoticRegularTrace.trace volume (regularRetained Y H B) ≤
      AsymptoticRegularTrace.trace volume B := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    change (matrix ((AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
      ((B z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) 1 1).re ≤ _
    rw [regular_corner_sandwich_root]
    classical
    by_cases hz : z ∈ retainedRegion Y H
    · simp only [Set.indicator_of_mem hz]
      exact le_refl _
    · simp only [Set.indicator_of_notMem hz,Complex.zero_re]
      exact root_nonneg _ (hp z)
  have hle : signedTrace volume (regularRetained Y H B) ≤ signedTrace volume B := by
    rw [signedTrace_eq_toReal volume _ (regularRetained_matrix_measurable Y H B hm 1 1) hpr,
      signedTrace_eq_toReal volume B (hm 1 1) hp]
    exact ENNReal.toReal_mono (observationRegularFilter_trace_finite A hN P e qs r s hs d).ne htr
  exact hle.trans_eq (observationRegularFilter_trace_eq_source A hN P e qs r s hs d)

#print axioms observationRegularFilter_trace_eq_source
#print axioms observationRegularFilter_positive
#print axioms observationRegularFilter_trace_finite
#print axioms observationRegularFilter_retained_trace_le_source

end QuantitativeHolomorphic
