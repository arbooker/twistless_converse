module

public import AsymptoticConcreteCountUpperV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSectorComparison

open Filter

/-- Reindex positive even weights without imposing a sector dimension
formula or changing the asymptotic filter. -/
theorem linearUpper_of_even_index (v : ℕ → ℝ) (c : ℝ)
    (hv : ∀ δ : ℝ,0<δ → ∀ᶠ h : ℕ in atTop,v (2*(h+1))≤(c+δ)*(2*h+2:ℕ)) :
    LinearUpper v c := by
  intro δ hδ
  obtain ⟨H,hH⟩ := eventually_atTop.mp (hv δ hδ)
  have he : ∀ᶠ k in evenWeights,Even k :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [(eventually_ge_atTop (2*(H+1))).filter_mono inf_le_left,he] with k hk heven
  obtain ⟨l,hl⟩ := heven
  have hh : H≤l-1 := by omega
  have hke : 2*((l-1)+1)=k := by omega
  have hke' : 2*(l-1)+2=k := by omega
  simpa only [hke,hke'] using hH (l-1) hh

#print axioms linearUpper_of_even_index

end AsymptoticSectorComparison

namespace AsymptoticCompactObservationCount

open UpperHalfPlane Set Filter FinitenessCertificate FinitenessGlobalHeight FinitenessOriginalInput
open AsymptoticSectorComparison Asymptotics

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The remaining analytic input is only approximation of the SUM of
regular traces by the desired total leading coefficient. The actual
count bound and large-weight trace limit have already been proved. -/
theorem count_upper_of_regular_approximation (hN : 0<N) (P : Parameters A) (c : ℝ)
    (happrox : ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r : Fin m → Row N,∃ s : Fin m → Set ℍ,
      ∃ hs : ∀ i,IsCompact (s i),totalRegularTrace A hN P r s hs≤4*Real.pi*c+η) :
    LinearUpper (fun k => ((S N k).ncard:ℝ)) c := by
  apply linearUpper_of_even_index
  intro δ hδ
  have hπ : 0<4*Real.pi := by positivity
  obtain ⟨m,r,s,hs,hr⟩ := happrox (4*Real.pi*(δ/2)) (by positivity)
  have hb : totalRegularTrace A hN P r s hs/(4*Real.pi)≤c+δ/2 :=
    (div_le_iff₀ hπ).mpr (by nlinarith)
  filter_upwards [count_upper_of_fixed_observations A hN P r s hs (by positivity : 0<δ/2)] with h hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- A concrete reduction to the regular total-trace approximation and the
TOTAL classical newspace lower bound/asymptotic. There are no individual
sector dimension hypotheses. These remaining inputs are explicit. -/
theorem count_littleO_of_regular_approximation_and_total_dimension
    (hN : 0<N) (P : Parameters A) (c : ℝ) (dimension : ℕ → ℕ)
    (happrox : ∀ η : ℝ,0<η → ∃ m : ℕ,∃ r : Fin m → Row N,∃ s : Fin m → Set ℍ,
      ∃ hs : ∀ i,IsCompact (s i),totalRegularTrace A hN P r s hs≤4*Real.pi*c+η)
    (hlower : ∀ᶠ k in evenWeights,dimension k≤(S N k).ncard)
    (hdimension : (fun k => (dimension k:ℝ)-c*(k:ℝ))=o[evenWeights] (fun k => (k:ℝ))) :
    (fun k => ((S N k).ncard:ℝ)-(dimension k:ℝ))=o[evenWeights] (fun k => (k:ℝ)) := by
  have hu := count_upper_of_regular_approximation A hN P c happrox
  apply count_from_total_dimension (ι:=Unit) (fun k => ((S N k).ncard:ℝ))
    (fun k => (dimension k:ℝ)) (fun _ k => ((S N k).ncard:ℝ)) (fun _ => c) (fun _ => hu)
  · filter_upwards [hlower] with k hk
    exact_mod_cast hk
  · exact Filter.Eventually.of_forall (fun _ => by simp)
  · simpa only [Fintype.sum_unique] using hdimension

#print axioms count_upper_of_regular_approximation
#print axioms count_littleO_of_regular_approximation_and_total_dimension

end AsymptoticCompactObservationCount
