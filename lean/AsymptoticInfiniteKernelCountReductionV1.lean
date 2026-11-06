module

public import AsymptoticRegularInfiniteKernelV1
public import AsymptoticFiniteKernelCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCompactObservationCount

open UpperHalfPlane MeasureTheory Filter FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticSectorComparison Asymptotics FinitenessOriginalInput
open scoped Topology

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def totalInfiniteKernelTrace (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  ∑ e : Sector N,(AsymptoticRegularTrace.trace volume
    (AsymptoticRegularObservation.infiniteKernelProjection A hN P r s hs e)).toReal

/-- Summing the actual sector traces commutes with approximation by finite
prefixes of a countable family of compact equations. -/
theorem finite_totalKernelTrace_tendsto (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    Tendsto (fun n => totalKernelTrace A hN P
      (fun i : Fin n => r i) (fun i => s i) (fun i => hs i)) atTop
      (𝓝 (totalInfiniteKernelTrace A hN P r s hs)) := by
  exact tendsto_finsetSum Finset.univ
    (fun e _ => AsymptoticRegularObservation.finiteKernelTrace_tendsto_infinite A hN P r s hs e)

/-- A single bound on the sum of the full joint-kernel traces supplies
all finite observation approximations needed by the analytic count. -/
theorem kernel_approx_of_infinite_kernel_bound (hN : 0<N) (P : Parameters A)
    (r : ℕ → Row N) (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (c : ℝ)
    (hk : totalInfiniteKernelTrace A hN P r s hs≤4*Real.pi*c) :
    ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r' : Fin m → Row N,∃ s' : Fin m → Set ℍ,
      ∃ hs' : ∀ i,IsCompact (s' i),totalKernelTrace A hN P r' s' hs'≤4*Real.pi*c+η := by
  intro η hη
  have ht := (tendsto_order.mp (finite_totalKernelTrace_tendsto A hN P r s hs)).2
    (totalInfiniteKernelTrace A hN P r s hs+η) (by linarith)
  obtain ⟨n,hn⟩ := ht.exists
  exact ⟨n,fun i => r i,fun i => s i,fun i => hs i,by linarith⟩

/-- This reduction proves normality, amplification and the large-weight
trace transfer. Its remaining hypotheses are the geometric full-kernel
bound and classical TOTAL newspace inputs; no sector dimension formula
is used. Those hypotheses are not yet discharged here. -/
theorem count_littleO_of_infinite_kernel_bound_and_total_dimension
    (hN : 0<N) (P : Parameters A) (r : ℕ → Row N) (s : ℕ → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (c : ℝ) (dimension : ℕ → ℕ)
    (hk : totalInfiniteKernelTrace A hN P r s hs≤4*Real.pi*c)
    (hlower : ∀ᶠ k in evenWeights,dimension k≤(S N k).ncard)
    (hdimension : (fun k => (dimension k:ℝ)-c*(k:ℝ))=o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => ((S N k).ncard:ℝ)-(dimension k:ℝ))=o[evenWeights] (fun k => (k:ℝ)) :=
  count_littleO_of_kernel_approximation_and_total_dimension A hN P c dimension
    (kernel_approx_of_infinite_kernel_bound A hN P r s hs c hk) hlower hdimension

#print axioms finite_totalKernelTrace_tendsto
#print axioms kernel_approx_of_infinite_kernel_bound
#print axioms count_littleO_of_infinite_kernel_bound_and_total_dimension

end AsymptoticCompactObservationCount
