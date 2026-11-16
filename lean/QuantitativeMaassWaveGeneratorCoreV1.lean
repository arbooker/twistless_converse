module

public import QuantitativeMaassQuotientWaveV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The twice-resolvent range is an actual graph core for the constructed
Friedrichs realization. This does not assert that the original compact
Poincaré domain is an operator graph core. -/
theorem twiceResolvent_graph_core (N : ℕ) :
    closure (Set.range (fun v : AutomorphicSpace N =>
      (friedrichsResolvent N (friedrichsResolvent N v),
        friedrichsResolvent N v-friedrichsResolvent N (friedrichsResolvent N v))))=
      {p : AutomorphicSpace N × AutomorphicSpace N | FriedrichsGraph N p.1 p.2} := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨v,rfl⟩
      exact friedrichsGraph_resolvent N (friedrichsResolvent N v)
    · exact friedrichsGraph_closed N
  · intro p hp
    let F : AutomorphicSpace N → AutomorphicSpace N × AutomorphicSpace N :=
      fun z => (friedrichsResolvent N z,z-friedrichsResolvent N z)
    have hF : Continuous F := (friedrichsResolvent N).continuous.prodMk
      (continuous_id.sub (friedrichsResolvent N).continuous)
    have h := mem_closure_image hF.continuousAt
      (friedrichsResolvent_denseRange N (p.1+p.2))
    have he : F (p.1+p.2)=p := by
      apply Prod.ext
      · exact hp
      · change p.1+p.2-friedrichsResolvent N (p.1+p.2)=p.2
        rw [hp]
        abel
    rw [he,← Set.range_comp] at h
    exact h

#print axioms twiceResolvent_graph_core

end QuantitativeMaass.Wave
