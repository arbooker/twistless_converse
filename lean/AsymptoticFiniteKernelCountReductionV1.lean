module

public import AsymptoticRegularKernelApproximationV1
public import AsymptoticObservationReindexV1
public import AsymptoticConcreteCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCompactObservationCount

open UpperHalfPlane MeasureTheory Filter FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticSectorComparison Asymptotics FinitenessOriginalInput
open scoped Topology

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable {ι : Type*} [Fintype ι]

noncomputable def totalKernelTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) : ℝ :=
  ∑ e : Sector N,(AsymptoticRegularTrace.trace volume
    (AsymptoticRegularObservation.jointKernelProjection A hN P r s hs e)).toReal

theorem repeated_totalTrace_tendsto (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    Tendsto (fun n : ℕ => totalRegularTrace A hN P
      (fun j : Fin ((n+1)^2) × ι => r j.2) (fun j => s j.2) (fun j => hs j.2)) atTop
      (𝓝 (totalKernelTrace A hN P r s hs)) := by
  exact tendsto_finsetSum Finset.univ
    (fun e _ => AsymptoticRegularObservation.repeatedPositive_trace_tendsto A hN P r s hs e)

/-- A small trace for one finite joint kernel yields a finite family of
known equations with equally small positive-operator trace. Repetition
and reindexing, rather than a new type of observation, provide the penalty. -/
theorem finite_observations_near_kernel (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {δ : ℝ} (hδ : 0<δ) :
    ∃ m : ℕ,∃ r' : Fin m → Row N,∃ s' : Fin m → Set ℍ,∃ hs' : ∀ i,IsCompact (s' i),
      totalRegularTrace A hN P r' s' hs'<totalKernelTrace A hN P r s hs+δ := by
  have ht := (tendsto_order.mp (repeated_totalTrace_tendsto A hN P r s hs)).2
    (totalKernelTrace A hN P r s hs+δ) (by linarith)
  obtain ⟨n,hn⟩ := ht.exists
  let κ := Fin ((n+1)^2) × ι
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ,fun j => r (e j).2,fun j => s (e j).2,fun j => hs (e j).2,?_⟩
  have he := totalRegularTrace_reindex A hN P (fun j : κ => r j.2)
    (fun j => s j.2) (fun j => hs j.2) e
  exact he.trans_lt hn

omit [Fintype ι] in
/-- The finite amplification step is proved. Only the geometric bound on
finite joint-kernel traces remains in this analytic approximation input. -/
theorem regular_approx_of_kernel_approx (hN : 0<N) (P : Parameters A) (c : ℝ)
    (hk : ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r : Fin m → Row N,∃ s : Fin m → Set ℍ,
      ∃ hs : ∀ i,IsCompact (s i),totalKernelTrace A hN P r s hs≤4*Real.pi*c+η) :
    ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r : Fin m → Row N,∃ s : Fin m → Set ℍ,
      ∃ hs : ∀ i,IsCompact (s i),totalRegularTrace A hN P r s hs≤4*Real.pi*c+η := by
  intro η hη
  have hη2 : 0<η/2 := by positivity
  obtain ⟨m,r,s,hs,hr⟩ := hk (η/2) hη2
  obtain ⟨m',r',s',hs',ht⟩ := finite_observations_near_kernel A hN P r s hs hη2
  exact ⟨m',r',s',hs',by linarith⟩

omit [Fintype ι] in
/-- The concrete summed count reduction after discharging amplification
and trace continuity. The remaining kernel bound and classical TOTAL
newspace inputs are explicit; this is not yet Theorem 1.2. -/
theorem count_littleO_of_kernel_approximation_and_total_dimension
    (hN : 0<N) (P : Parameters A) (c : ℝ) (dimension : ℕ → ℕ)
    (hk : ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r : Fin m → Row N,∃ s : Fin m → Set ℍ,
      ∃ hs : ∀ i,IsCompact (s i),totalKernelTrace A hN P r s hs≤4*Real.pi*c+η)
    (hlower : ∀ᶠ k in evenWeights,dimension k≤(S N k).ncard)
    (hdimension : (fun k => (dimension k:ℝ)-c*(k:ℝ))=o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => ((S N k).ncard:ℝ)-(dimension k:ℝ))=o[evenWeights] (fun k => (k:ℝ)) :=
  count_littleO_of_regular_approximation_and_total_dimension A hN P c dimension
    (regular_approx_of_kernel_approx A hN P c hk) hlower hdimension

#print axioms repeated_totalTrace_tendsto
#print axioms finite_observations_near_kernel
#print axioms regular_approx_of_kernel_approx
#print axioms count_littleO_of_kernel_approximation_and_total_dimension

end AsymptoticCompactObservationCount
