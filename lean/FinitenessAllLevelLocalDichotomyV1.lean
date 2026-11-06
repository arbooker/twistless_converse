module

public import FinitenessAllLevelLocalGraphV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelQuadraticCoordinates FinitenessAllLevelAnalyticSubstitution
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Finite ι] {R : ℂ → X → Prop}

/-- At a generic parameter, each actual solution point is either isolated
or lies on a holomorphic graph of ACTUAL solutions. Every equation is checked
on the graph. Scalar root branches alone are not counted as solution curves. -/
theorem Presentation.RootModel.local_dichotomy (c : Presentation ι R) {w : c.U}
    (hm : c.RootModel w) (v : Fin c.n → ℂ)
    (hv : ∀ j, evaluate v (c.coefficients j w) = 0) :
    (∃ B : ℂ → (Fin c.n → ℂ), B w = v ∧ AnalyticAt ℂ B w ∧
      AnalyticAt ℂ (fun z => c.lift z (B z)) w ∧
      (∀ᶠ z in 𝓝 w.val, R z (c.lift z (B z))) ∧
      ∀ᶠ t in 𝓝 (w.val, v),
        (t.1 ∈ c.U ∧ ∀ j, evaluate t.2 (c.coefficients j t.1) = 0) ↔ t.2 = B t.1) ∨
    (∀ᶠ t in 𝓝 (w.val, v),
      (t.1 ∈ c.U ∧ ∀ j, evaluate t.2 (c.coefficients j t.1) = 0) ↔ t = (w.val, v)) := by
  obtain ⟨B, hBw, hB, hcontain⟩ := hm.local_graph c v hv
  have hU : ∀ᶠ z in 𝓝 w.val, z ∈ c.U := c.openU.mem_nhds w.property
  have hfst : Tendsto (fun t : ℂ × (Fin c.n → ℂ) => t.1)
      (𝓝 (w.val, v)) (𝓝 w.val) := continuous_fst.continuousAt.tendsto
  rcases c.graph_dichotomy w.property hB with hall | hnone
  · refine Or.inl ⟨B, hBw, hB, ?_, ?_, ?_⟩
    · exact (joint_analytic c.analytic_lift (w.val, B w)
        ⟨w.property, mem_univ _⟩).comp (f := fun z : ℂ => (z, B z)) (analyticAt_id.prod hB)
    · filter_upwards [hU, hall] with z hz he
      exact (c.exact_locus z hz _).mpr ⟨B z, he, rfl⟩
    · filter_upwards [hcontain, hfst.eventually hall, hfst.eventually hU] with t ht he hu
      constructor
      · exact ht
      · intro hb
        exact ⟨hu, hb ▸ he⟩
  · have hn : ∀ᶠ z in 𝓝 w.val, z ≠ w.val →
        ¬ ∀ j, evaluate (B z) (c.coefficients j z) = 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp hnone
    refine Or.inr ?_
    filter_upwards [hcontain, hfst.eventually hn] with t ht hn'
    constructor
    · intro hs
      have hb := ht hs
      have hz : t.1 = w.val := by
        by_contra hz
        exact hn' hz (hb ▸ hs.2)
      exact Prod.ext hz (hb.trans (hz ▸ hBw))
    · rintro rfl
      exact ⟨w.property, hv⟩

#print axioms Presentation.RootModel.local_dichotomy

end FinitenessAllLevelPolynomialPresentation
