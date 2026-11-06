module

public import FinitenessAllLevelLocalReadV1
public import FinitenessAllLevelRegularGraphsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
  FinitenessAllLevelAnalyticSubstitution
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Finite ι] {R : ℂ → X → Prop}

/-- The local graph property in the actual ambient topology. -/
def AmbientGraphAt (R : ℂ → X → Prop) (w : ℂ) (x : X) : Prop :=
  ∃ F : ℂ → X, F w = x ∧ AnalyticAt ℂ F w ∧
    (∀ᶠ z in 𝓝 w, R z (F z)) ∧
    ∀ᶠ t in 𝓝 (w, x), R t.1 t.2 ↔ t.2 = F t.1

/-- The polynomial-coordinate graph is a genuine local graph in the
original Banach-space locus. This supplies both directions in ambient
neighborhoods, as required for finite-sheet continuation. -/
theorem Presentation.BranchCertificate.ambient_graph (c : Presentation ι R)
    (D : c.BranchCertificate) (w : c.U)
    (hw : evaluation c.U c.coefficientFunctions w D.exceptional ≠ 0)
    {x : X} (hx : R w x) : AmbientGraphAt R w x := by
  obtain ⟨v, hv, hxv⟩ := (c.exact_locus w w.property x).mp hx
  obtain ⟨B, hBw, _, hF, hsol, hgraph⟩ := D.local_graph c w hw v hv
  obtain ⟨read, hread, hleft⟩ := c.local_read w.property
  have hreadw : read w x = v := by rw [hxv]; exact (hleft.self_of_nhds) v
  have hcoord : ContinuousAt (fun t : ℂ × X => (t.1, read t.1 t.2)) (w.val, x) :=
    continuousAt_fst.prodMk ((hread.continuousAt.comp (f := fun t : ℂ × X => t.1) continuousAt_fst).clm_apply continuousAt_snd)
  have hcoord' : Tendsto (fun t : ℂ × X => (t.1, read t.1 t.2))
      (𝓝 (w.val, x)) (𝓝 (w.val, v)) := by
    simpa only [hreadw] using hcoord.tendsto
  have hfst : Tendsto (fun t : ℂ × X => t.1) (𝓝 (w.val, x)) (𝓝 w.val) :=
    continuous_fst.continuousAt.tendsto
  refine ⟨fun z => c.lift z (B z), by change c.lift w (B w) = x; rw [hBw, ← hxv], hF, hsol, ?_⟩
  filter_upwards [hcoord'.eventually hgraph, hfst.eventually hleft,
    hfst.eventually (c.openU.mem_nhds w.property), hfst.eventually hsol] with t ht hl hu hs
  constructor
  · intro hr
    obtain ⟨u, he, hy⟩ := (c.exact_locus t.1 hu t.2).mp hr
    have hru : read t.1 t.2 = u := by rw [hy]; exact hl u
    have hb : read t.1 t.2 = B t.1 := ht.mp ⟨hu, by rwa [hru]⟩
    rw [hy, ← hb, hru]
  · intro he
    exact he ▸ hs

#print axioms Presentation.BranchCertificate.ambient_graph

end FinitenessAllLevelPolynomialPresentation
