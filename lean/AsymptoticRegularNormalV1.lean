module

public import AsymptoticRegularTraceV1
public import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Filter ContinuousLinearMap InnerProductSpace
open scoped lp ENNReal Topology

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem root_nonneg (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : B.IsPositive) :
    0≤(matrix B 1 1).re := by
  rw [matrix,← delta_inner]
  exact hB.re_inner_nonneg_right _

/-- Additivity of the rooted weight on positive measurable operator
families, including infinite trace. -/
theorem trace_add (μ : Measure α) (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : Measurable (fun x => matrix (B x) 1 1))
    (hB : ∀ x, (B x).IsPositive) (hC : ∀ x, (C x).IsPositive) :
    trace μ (fun x => B x+C x)=trace μ B+trace μ C := by
  have he (x : α) : ENNReal.ofReal (matrix (B x+C x) 1 1).re=
      ENNReal.ofReal (matrix (B x) 1 1).re+ENNReal.ofReal (matrix (C x) 1 1).re := by
    simp only [matrix,add_apply,lp.coeFn_add,Pi.add_apply,Complex.add_re]
    exact ENNReal.ofReal_add (root_nonneg _ (hB x)) (root_nonneg _ (hC x))
  simp_rw [trace,he]
  exact lintegral_add_left (Complex.continuous_re.measurable.comp hm).ennreal_ofReal _

/-- Countable normality of the rooted weight: an increasing family with
a weak operator limit has the corresponding monotone trace limit. This
also applies when the limiting trace is infinite. -/
theorem trace_monotone_limit (μ : Measure α)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (Q : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ n, Measurable (fun x => matrix (B n x) 1 1))
    (hmono : ∀ x n m, n≤m → (B m x-B n x).IsPositive)
    (hweak : ∀ x v w, Tendsto (fun n => ⟪v,B n x w⟫_ℂ) atTop (𝓝 ⟪v,Q x w⟫_ℂ)) :
    Tendsto (fun n => trace μ (B n)) atTop (𝓝 (trace μ Q)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (Complex.continuous_re.measurable.comp (hm n)).ennreal_ofReal.aemeasurable)
  · apply Filter.Eventually.of_forall
    intro x n m hnm
    apply ENNReal.ofReal_le_ofReal
    have hp := root_nonneg (B m x-B n x) (hmono x n m hnm)
    simp only [matrix,sub_apply,lp.coeFn_sub,Pi.sub_apply,Complex.sub_re] at hp
    exact sub_nonneg.mp hp
  · apply Filter.Eventually.of_forall
    intro x
    have ht := hweak x (delta 1) (delta 1)
    simp only [delta_inner] at ht
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp ht)

#print axioms trace_add
#print axioms trace_monotone_limit

end AsymptoticRegularTrace
