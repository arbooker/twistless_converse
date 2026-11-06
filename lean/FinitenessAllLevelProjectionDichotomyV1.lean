module

public import FinitenessAllLevelRegularGraphsV1
public import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Finite ι] {R : ℂ → X → Prop}

/-- A regular actual solution gives an open neighborhood in the projection. -/
theorem Presentation.BranchCertificate.mem_interior_projection (c : Presentation ι R)
    (D : c.BranchCertificate) (w : c.U)
    (hw : evaluation c.U c.coefficientFunctions w D.exceptional ≠ 0)
    (hx : ∃ x, R w x) : w.val ∈ interior {z | ∃ x, R z x} := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨v, hv, _⟩ := (c.exact_locus w w.property x).mp hx
  obtain ⟨B, _, _, _, he, _⟩ := D.local_graph c w hw v hv
  apply mem_interior_iff_mem_nhds.mpr
  exact he.mono (fun z hz => ⟨c.lift z (B z), hz⟩)

/-- Every parameter has a punctured neighborhood on which the projection
has no boundary points belonging to the projection. -/
theorem Presentation.punctured_interior_projection (c : Presentation ι R)
    (hconn : IsPreconnected c.U)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite)
    {w : ℂ} (hw : w ∈ c.U) :
    ∀ᶠ z in 𝓝[≠] w, (∃ x, R z x) → z ∈ interior {z | ∃ x, R z x} := by
  obtain ⟨D⟩ := c.exists_branchCertificate hconn ⟨w, hw⟩ hf
  have hU : ∀ᶠ z in 𝓝[≠] w, z ∈ c.U := nhdsWithin_le_nhds (c.openU.mem_nhds hw)
  have hn := representative_nonzero_punctured c.coefficientFunctions hconn
    c.coefficientFunctions_analytic D.exceptional_ne_zero hw
  filter_upwards [hU, hn] with z hz he hx
  apply D.mem_interior_projection c ⟨z, hz⟩ ?_ hx
  change D.exceptional.val ⟨z, hz⟩ ≠ 0
  rwa [representative_agrees (z := ⟨z, hz⟩)] at he

/-- A closed planar set with the preceding punctured openness property is
either the entire plane or discrete. This uses connectedness of the
complement of a countable subset of the plane, not proper mapping theory. -/
theorem closed_projection_dichotomy (S : Set ℂ) (hS : IsClosed S)
    (hlocal : ∀ w : ℂ, ∀ᶠ z in 𝓝[≠] w, z ∈ S → z ∈ interior S) :
    S = univ ∨ IsDiscrete S := by
  have hdisc : IsDiscrete (frontier S) := by
    apply (compl_mem_codiscrete_iff.mp ?_).2
    apply mem_codiscrete_iff_forall_mem_nhdsNE.mpr
    intro w
    filter_upwards [hlocal w] with z hz
    intro hfront
    have hi := hz (hS.frontier_subset hfront)
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hi hfront
  have hcount : (frontier S).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  have hconn := (hcount.isConnected_compl_of_one_lt_rank
    (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))).isPreconnected
  have hcover : (frontier S)ᶜ ⊆ interior S ∪ Sᶜ := by
    rw [compl_frontier_eq_union_interior]
    exact Set.union_subset_union (Subset.refl _) interior_subset
  have hdisj : Disjoint (interior S) Sᶜ :=
    Set.disjoint_left.mpr (fun z hz hn => hn (interior_subset hz))
  rcases hconn.subset_or_subset isOpen_interior hS.isOpen_compl hdisj hcover with hall | hnone
  · left
    apply eq_univ_of_univ_subset
    rw [← (hcount.dense_compl ℂ).closure_eq]
    exact closure_minimal (hall.trans interior_subset) hS
  · right
    apply hdisc.mono
    intro z hz
    by_contra hn
    exact hnone hn hz

#print axioms Presentation.BranchCertificate.mem_interior_projection
#print axioms Presentation.punctured_interior_projection
#print axioms closed_projection_dichotomy

end FinitenessAllLevelPolynomialPresentation
