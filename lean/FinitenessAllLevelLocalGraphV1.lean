module

public import FinitenessAllLevelSectorRootModelsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

/-- At a parameter with simple coordinate root models, the actual common
zero set near any of its points is contained in a single holomorphic graph.
This follows from the uniqueness of every scalar root branch. -/
theorem Presentation.RootModel.local_graph (c : Presentation ι R) {w : c.U}
    (hm : c.RootModel w) (v : Fin c.n → ℂ)
    (hv : ∀ j, evaluate v (c.coefficients j w) = 0) :
    ∃ B : ℂ → (Fin c.n → ℂ), B w = v ∧ AnalyticAt ℂ B w ∧
      ∀ᶠ t in 𝓝 (w.val, v),
        (t.1 ∈ c.U ∧ ∀ j, evaluate t.2 (c.coefficients j t.1) = 0) → t.2 = B t.1 := by
  classical
  choose q _ _ hzero hbranch using hm
  have hb (i : Fin c.n) : ∃ b : ℂ → ℂ, b w = v i ∧ AnalyticAt ℂ b w ∧
      ∀ᶠ t in 𝓝 (w.val, v i), polynomialEquation c.coefficientFunctions (q i) t = 0 ↔
        b t.1 = t.2 := by
    have hr := hzero i w v hv
    rw [polynomialEquation_eq] at hr
    obtain ⟨b, hb, ha, _, hu⟩ := hbranch i (v i) hr
    exact ⟨b, hb, ha, hu⟩
  choose b hb ha hu using hb
  refine ⟨fun z i => b i z, funext hb, AnalyticAt.pi ha, ?_⟩
  have hall : ∀ᶠ t : ℂ × (Fin c.n → ℂ) in 𝓝 (w.val, v), ∀ i : Fin c.n,
      polynomialEquation c.coefficientFunctions (q i) (t.1, t.2 i) = 0 ↔ b i t.1 = t.2 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℂ × (Fin c.n → ℂ) => (t.1, t.2 i)) (w.val, v) := by
      fun_prop
    exact hc.tendsto.eventually (hu i)
  filter_upwards [hall] with t ht hs
  ext i
  exact ((ht i).mp (hzero i ⟨t.1, hs.1⟩ t.2 hs.2)).symm

/-- Substituting a holomorphic coordinate graph into the actual quadratic
equations preserves holomorphy. -/
theorem Presentation.graph_equation_analytic (c : Presentation ι R) {w : ℂ} (hw : w ∈ c.U)
    {B : ℂ → (Fin c.n → ℂ)} (hB : AnalyticAt ℂ B w) (j : ι) :
    AnalyticAt ℂ (fun z => evaluate (B z) (c.coefficients j z)) w := by
  have hc := c.analytic_coefficients j w hw
  have he (e : Entry c.n) := (entry e).toContinuousLinearMap.analyticAt (c.coefficients j w)
  have hb (i : Fin c.n) := ((ContinuousLinearMap.proj i).analyticAt (B w)).comp hB
  change AnalyticAt ℂ (fun z => (c.coefficients j z).1 +
    (∑ i, (c.coefficients j z).2.1 i * B z i) +
    ∑ i, ∑ k, (c.coefficients j z).2.2 i k * B z i * B z k) w
  apply AnalyticAt.add
  · exact ((he (.inl ())).comp hc).add
      (Finset.analyticAt_fun_sum _ (fun i _ => ((he (.inr (.inl i))).comp hc).mul (hb i)))
  · apply Finset.analyticAt_fun_sum
    intro i _
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (((he (.inr (.inr (i, k)))).comp hc).mul (hb i)).mul (hb k)

/-- On a candidate graph, finitely many analytic equations either all hold
near the parameter or have no simultaneous zeros in a punctured neighborhood.
This is derived from isolated zeros, not assumed as analytic-space theory. -/
theorem Presentation.graph_dichotomy [Finite ι] (c : Presentation ι R)
    {w : ℂ} (hw : w ∈ c.U) {B : ℂ → (Fin c.n → ℂ)} (hB : AnalyticAt ℂ B w) :
    (∀ᶠ z in 𝓝 w, ∀ j, evaluate (B z) (c.coefficients j z) = 0) ∨
      (∀ᶠ z in 𝓝[≠] w, ¬ ∀ j, evaluate (B z) (c.coefficients j z) = 0) := by
  classical
  by_cases h : ∀ j, ∀ᶠ z in 𝓝 w, evaluate (B z) (c.coefficients j z) = 0
  · exact Or.inl (Filter.eventually_all.mpr h)
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have he := (c.graph_equation_analytic hw hB j).eventually_eq_zero_or_eventually_ne_zero
    refine Or.inr ((he.resolve_left hj).mono ?_)
    intro z hz hzero
    exact hz (hzero j)

#print axioms Presentation.RootModel.local_graph
#print axioms Presentation.graph_equation_analytic
#print axioms Presentation.graph_dichotomy

end FinitenessAllLevelPolynomialPresentation
