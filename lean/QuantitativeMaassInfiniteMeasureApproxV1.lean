module

public import QuantitativeMaassAllLevelAbelNormalizedV1
public import QuantitativeMaassPoincareComplexUnfoldV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Contractions converge strongly once their diagonal inner products
converge. This criterion does not require finite underlying measure. -/
theorem contraction_inner_tendsto {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (l : Filter ι) (u : ι → E) (f : E)
    (hu : ∀ᶠ i in l, ‖u i‖≤‖f‖)
    (hi : Tendsto (fun i => (inner ℂ (u i) f).re) l (𝓝 (‖f‖^2))) :
    Tendsto u l (𝓝 f) := by
  have hs : Tendsto (fun i => ‖u i-f‖^2) l (𝓝 0) := by
    have hb : ∀ᶠ i in l, ‖u i-f‖^2≤‖f‖^2-2*(inner ℂ (u i) f).re+‖f‖^2 := by
      filter_upwards [hu] with i hi
      rw [norm_sub_sq (𝕜:=ℂ)]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hi 2
      change ‖u i‖^2-2*(inner ℂ (u i) f).re+‖f‖^2 ≤
        ‖f‖^2-2*(inner ℂ (u i) f).re+‖f‖^2
      linarith only [hsq]
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hb
    have h := ((tendsto_const_nhds (x:=‖f‖^2)).sub (hi.const_mul 2)).add
      (tendsto_const_nhds (x:=‖f‖^2))
    simpa only [show ‖f‖^2-2*‖f‖^2+‖f‖^2=0 by ring] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using ht

/-- Dominated convergence against an L1 test replaces the invalid use of a
constant integrable majorant on an infinite-volume quotient. -/
theorem bounded_L1_diagonal_tendsto {ι α : Type*} [MeasurableSpace α]
    (μ : Measure α) (l : Filter ι) [l.IsCountablyGenerated]
    (F : ι → α → ℂ) (f : α → ℂ)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) (hf : Integrable f μ)
    (B : ℝ) (_hB : 0≤B) (hb : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖≤B)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => ∫ x,star (F i x)*f x ∂μ) l
      (𝓝 (∫ x,star (f x)*f x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => B*‖f x‖)
  · exact Eventually.of_forall (fun i => (hF i).star.mul hf.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro i
    filter_upwards [hb i] with x hx
    rw [norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  · exact hf.norm.const_mul B
  · filter_upwards [ht] with x hx
    exact hx.star.mul tendsto_const_nhds

#print axioms contraction_inner_tendsto
#print axioms bounded_L1_diagonal_tendsto

end QuantitativeMaass
