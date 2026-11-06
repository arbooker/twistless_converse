module

public import AsymptoticConcreteTraceLimitV1
public import AsymptoticSectorComparisonV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCompactObservationCount

open UpperHalfPlane Set Filter FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open FinitenessOriginalInput
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def totalRegularTrace (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  ∑ e : Sector N,(AsymptoticRegularTrace.trace MeasureTheory.volume
    (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal

theorem count_le_holomorphicTraces (hN : 0<N) (P : Parameters A) (h : ℕ)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    ((S N (2*(h+1))).ncard:ℝ)≤
      ∑ e : Sector N,AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e := by
  simpa only [AsymptoticCylinderObservation.holomorphicTrace,AsymptoticCylinderObservation.positive,
    AsymptoticObservation.holomorphicOperator,AsymptoticReconstructedCount.includedReconstruction]
    using count_le_traces A hN P h r s hs

/-- Add the actual sector traces before comparing with a classical total
dimension. No individual sector dimension formula is used. -/
theorem sum_holomorphicTraces_limit (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    Tendsto (fun h : ℕ =>
      (∑ e : Sector N,AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e)/(2*h+2:ℕ))
      atTop (𝓝 (totalRegularTrace A hN P r s hs/(4*Real.pi))) := by
  have ht := tendsto_finsetSum Finset.univ
    (fun e _ => AsymptoticSharedApproximation.holomorphic_trace_limit A hN P r s hs e)
  simpa only [totalRegularTrace,Finset.sum_div] using ht

theorem count_upper_of_fixed_observations (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ h : ℕ in atTop, ((S N (2*(h+1))).ncard:ℝ)≤
      (totalRegularTrace A hN P r s hs/(4*Real.pi)+δ)*(2*h+2:ℕ) := by
  have ht := (tendsto_order.mp (sum_holomorphicTraces_limit A hN P r s hs)).2
    (totalRegularTrace A hN P r s hs/(4*Real.pi)+δ) (by linarith)
  filter_upwards [ht] with h hh
  exact (count_le_holomorphicTraces A hN P h r s hs).trans
    ((div_lt_iff₀ (by positivity : (0:ℝ)<(2*h+2:ℕ))).mp hh).le

#print axioms count_le_holomorphicTraces
#print axioms sum_holomorphicTraces_limit
#print axioms count_upper_of_fixed_observations

end AsymptoticCompactObservationCount
