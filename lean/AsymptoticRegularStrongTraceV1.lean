module

public import AsymptoticRegularTraceV1
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Filter ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct Topology ENNReal

variable {G α : Type*} [Group G]

omit [Group G] in
/-- Strong convergence gives convergence of every counting-coordinate
matrix coefficient. No operator-norm convergence is required. -/
theorem matrix_tendsto_of_strong
    (B : ℕ → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ v,Tendsto (fun n => B n v) atTop (𝓝 (C v))) (g h : G) :
    Tendsto (fun n => matrix (B n) g h) atTop (𝓝 (matrix C g h)) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => delta g) atTop (𝓝 (delta g))).inner (𝕜:=ℂ) (hB (delta h))
  simpa only [delta_inner,matrix] using ht

variable [MeasurableSpace α]

omit [Group G] in
theorem strong_limit_matrix_measurable
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ n g h,Measurable (fun x => matrix (B n x) g h))
    (hB : ∀ x v,Tendsto (fun n => B n x v) atTop (𝓝 (C x v))) (g h : G) :
    Measurable (fun x => matrix (C x) g h) :=
  measurable_of_tendsto_metrizable (fun n => hm n g h)
    (tendsto_pi_nhds.mpr (fun x => matrix_tendsto_of_strong (fun n => B n x) (C x) (hB x) g h))

/-- Domination by one finite rooted mass turns strong convergence into
convergence of the rooted trace, even on the infinite-area base. -/
theorem trace_tendsto_of_strong_dominated (μ : Measure α)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ n,Measurable (fun x => matrix (B n x) 1 1))
    (hB : ∀ x v,Tendsto (fun n => B n x v) atTop (𝓝 (C x v)))
    (bound : α → ℝ≥0∞) (hb : ∀ n x,ENNReal.ofReal (matrix (B n x) 1 1).re≤bound x)
    (hfin : ∫⁻ x,bound x ∂μ≠∞) :
    Tendsto (fun n => trace μ (B n)) atTop (𝓝 (trace μ C)) := by
  apply tendsto_lintegral_of_dominated_convergence bound
  · intro n
    exact (Complex.continuous_re.measurable.comp (hm n)).ennreal_ofReal
  · intro n
    exact Eventually.of_forall (hb n)
  · exact hfin
  · apply Eventually.of_forall
    intro x
    have ht := matrix_tendsto_of_strong (fun n => B n x) (C x) (hB x) 1 1
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp ht)

theorem trace_limit_finite_of_strong_dominated (μ : Measure α)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ x v,Tendsto (fun n => B n x v) atTop (𝓝 (C x v)))
    (bound : α → ℝ≥0∞) (hb : ∀ n x,ENNReal.ofReal (matrix (B n x) 1 1).re≤bound x)
    (hfin : ∫⁻ x,bound x ∂μ≠∞) : trace μ C<∞ := by
  apply lt_of_le_of_lt (b:=∫⁻ x,bound x ∂μ) _ (lt_top_iff_ne_top.mpr hfin)
  apply lintegral_mono
  intro x
  have ht := matrix_tendsto_of_strong (fun n => B n x) (C x) (hB x) 1 1
  have hl := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)
  exact le_of_tendsto hl (Eventually.of_forall (fun n => hb n x))

theorem trace_toReal_tendsto_of_strong_dominated (μ : Measure α)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ n,Measurable (fun x => matrix (B n x) 1 1))
    (hB : ∀ x v,Tendsto (fun n => B n x v) atTop (𝓝 (C x v)))
    (bound : α → ℝ≥0∞) (hb : ∀ n x,ENNReal.ofReal (matrix (B n x) 1 1).re≤bound x)
    (hfin : ∫⁻ x,bound x ∂μ≠∞) :
    Tendsto (fun n => (trace μ (B n)).toReal) atTop (𝓝 (trace μ C).toReal) :=
  (ENNReal.tendsto_toReal (trace_limit_finite_of_strong_dominated μ B C hB bound hb hfin).ne).comp
    (trace_tendsto_of_strong_dominated μ B C hm hB bound hb hfin)

#print axioms matrix_tendsto_of_strong
#print axioms strong_limit_matrix_measurable
#print axioms trace_tendsto_of_strong_dominated
#print axioms trace_limit_finite_of_strong_dominated
#print axioms trace_toReal_tendsto_of_strong_dominated

end AsymptoticRegularTrace
