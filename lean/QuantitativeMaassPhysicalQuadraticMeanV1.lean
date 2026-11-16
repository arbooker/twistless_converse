module

public import QuantitativeMaassCuspCenteredVariationV1
public import QuantitativeMaassAbelContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A finite physical Abel integral after horizontal and radial square substitutions. -/
def physicalQuadraticMean (F : ℝ → ℂ) (L v : ℝ) : ℂ :=
  ∫ s in Icc (0:ℝ) L,F (1+v^2/2+s^2)

theorem physicalQuadratic_integrand_smooth (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => F (1+p.1^2/2+p.2^2)) := by
  apply ContDiffOn.comp_contDiff hF (by fun_prop)
  intro p
  change 1≤1+p.1^2/2+p.2^2
  nlinarith [sq_nonneg p.1,sq_nonneg p.2]

theorem physicalQuadraticMean_continuous (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (L : ℝ) : Continuous (physicalQuadraticMean F L) :=
  continuous_parametric_integral_of_continuous (f:=fun v s => F (1+v^2/2+s^2))
    (physicalQuadratic_integrand_smooth F hF).continuous isCompact_Icc

/-- Differentiation only samples the physical half-line. The derivative bound
comes from a compact parameter rectangle, including its boundary. -/
theorem physicalQuadraticMean_hasDerivAt (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (L v : ℝ) :
    HasDerivAt (physicalQuadraticMean F L)
      (v • physicalQuadraticMean (derivWithin F (Ici 1)) L v) v := by
  let F₁ := derivWithin F (Ici 1)
  have hF₁ : ContDiffOn ℝ ∞ F₁ (Ici 1) := hF.derivWithin (uniqueDiffOn_Ici (1:ℝ)) (by simp)
  let D : ℝ → ℝ → ℂ := fun x s => x • F₁ (1+x^2/2+s^2)
  have hDc : Continuous (Function.uncurry D) :=
    continuous_fst.smul (physicalQuadratic_integrand_smooth F₁ hF₁).continuous
  have hFc := (physicalQuadratic_integrand_smooth F hF).continuous
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s:=Icc (v-1) (v+1) ×ˢ Icc (0:ℝ) L) hDc.continuousOn
  have hder (s x : ℝ) : HasDerivAt (fun w => F (1+w^2/2+s^2)) (D x s) x := by
    have hq : 1≤1+x^2/2+s^2 := by nlinarith [sq_nonneg x,sq_nonneg s]
    have hh := (hF.differentiableOn (by simp) _ hq).hasDerivWithinAt
    have hp : HasDerivAt (fun w : ℝ => 1+w^2/2+s^2) x x := by
      convert (((hasDerivAt_id x).pow 2).div_const 2).const_add 1 |>.add_const (s^2) using 1 <;> simp
    have hs (w : ℝ) : 1+w^2/2+s^2∈Ici (1:ℝ) := by
      change 1≤1+w^2/2+s^2
      nlinarith [sq_nonneg w,sq_nonneg s]
    simpa only [Function.comp_def,D,F₁] using hh.scomp_hasDerivAt x hp hs
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Icc (0:ℝ) L)) (F:=fun x s : ℝ => F (1+x^2/2+s^2))
    (F':=D) (bound:=fun _ => C) (s:=Ioo (v-1) (v+1))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun x => (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hFc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc)
    ((hDc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      intro x hx
      exact hC (x,s) ⟨⟨hx.1.le,hx.2.le⟩,hs⟩)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (Eventually.of_forall (fun s x _ => hder s x))
  have he : (∫ s in Icc (0:ℝ) L,D v s)=v • physicalQuadraticMean F₁ L v := by
    exact integral_smul v _
  rw [he] at hh
  exact hh.2

#print axioms physicalQuadratic_integrand_smooth
#print axioms physicalQuadraticMean_continuous
#print axioms physicalQuadraticMean_hasDerivAt

end QuantitativeMaass
