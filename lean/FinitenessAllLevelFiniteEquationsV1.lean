module

public import FinitenessAllLevelQuadraticCoordinatesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelQuadraticCoordinates

open Complex Set Filter Module
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n : ℕ} (b : Basis (Fin n) ℂ E) {U : Set ℂ}

/-- Common-domain analytic equations of degree at most two in finitely many
coordinates admit one finite subfamily defining the identical zero set near
each parameter. The neighborhood is uniform in all coordinate vectors. -/
theorem finite_equations_local (hU : IsOpen U) (hconn : IsPreconnected U)
    (H : ι → ℂ × E → ℂ) (hH : ∀ i, Representable b (U := U) (H i))
    {w : ℂ} (hw : w ∈ U) :
    ∃ s : Finset ι, ∀ᶠ z in 𝓝 w, ∀ v : E,
      (∀ i, H i (z, v) = 0) ↔ (∀ i ∈ s, H i (z, v) = 0) := by
  classical
  choose c hc he using hH
  obtain ⟨s, hs⟩ := FinitenessAllLevelAnalyticRank.finite_rows_local hU hconn c hc hw
  refine ⟨s, hs.mono ?_⟩
  intro z hz v
  constructor
  · exact fun h i _ => h i
  · intro h i
    have hk : Submodule.span ℂ ((fun i => c i z) '' (s : Set ι)) ≤
        LinearMap.ker (evaluate (b.repr v)) := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, hj, rfl⟩
      exact (he j z v).trans (h j hj)
    rw [hz] at hk
    exact (he i z v).symm.trans (hk (Submodule.subset_span (mem_range_self i)))

theorem finite_equations_neighborhood (hU : IsOpen U) (hconn : IsPreconnected U)
    (H : ι → ℂ × E → ℂ) (hH : ∀ i, Representable b (U := U) (H i))
    {w : ℂ} (hw : w ∈ U) :
    ∃ s : Finset ι, ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∀ z ∈ V, ∀ v : E, (∀ i, H i (z, v) = 0) ↔ (∀ i ∈ s, H i (z, v) = 0) := by
  obtain ⟨s, hs⟩ := finite_equations_local b hU hconn H hH hw
  obtain ⟨V, hV, hVo, hwV⟩ := mem_nhds_iff.mp (hs.and (hU.mem_nhds hw))
  exact ⟨s, V, hVo, hwV, fun z hz => (hV hz).2, fun z hz => (hV hz).1⟩

#print axioms finite_equations_local
#print axioms finite_equations_neighborhood

end FinitenessAllLevelQuadraticCoordinates
