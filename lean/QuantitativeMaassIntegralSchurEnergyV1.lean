module

public import QuantitativeMaassIntegralSchurRowV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass.IntegralSchur
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SFinite μ]

/-- The column bound makes the actual weighted square integrable on the
product space. This supplies the Fubini hypothesis rather than assuming it. -/
theorem energy_integrable (k : A → A → ℂ) (hk : Measurable (Function.uncurry k))
    {C : ℝ} (_hC : 0≤C) (hi : ∀ y,Integrable (fun x => k x y) μ)
    (hb : ∀ y,(∫ x,‖k x y‖ ∂μ)≤C)
    (f : A → ℂ) (hf : Measurable f) (hL : MemLp f 2 μ) :
    Integrable (fun p : A×A => ‖k p.1 p.2‖*‖f p.2‖^2) (μ.prod μ) ∧
    (∫ p : A×A,‖k p.1 p.2‖*‖f p.2‖^2 ∂μ.prod μ)≤C*(∫ y,‖f y‖^2 ∂μ) := by
  let E : A×A → ℝ := fun p => ‖k p.1 p.2‖*‖f p.2‖^2
  have hE : Measurable E := hk.norm.mul ((hf.comp measurable_snd).norm.pow_const 2)
  have hpos (p : A×A) : 0≤E p := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsec (y : A) : Integrable (fun x => E (x,y)) μ :=
    (hi y).norm.mul_const (‖f y‖^2)
  have hbound (y : A) : (∫ x,E (x,y) ∂μ)≤C*‖f y‖^2 := by
    dsimp only [E]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hb y) (sq_nonneg _)
  have hmarg : Integrable (fun y => ∫ x,E (x,y) ∂μ) μ := by
    apply (hL.norm.integrable_sq.const_mul C).mono'
      hE.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => hpos (x,y)))]
    exact hbound y
  have hprod : Integrable E (μ.prod μ) := by
    apply (integrable_prod_iff' hE.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hsec,?_⟩
    simpa only [Real.norm_of_nonneg (hpos _)] using hmarg
  refine ⟨hprod,?_⟩
  change (∫ p,E p ∂μ.prod μ)≤_
  rw [integral_prod_symm E hprod,← integral_const_mul]
  exact integral_mono hmarg (hL.norm.integrable_sq.const_mul C) hbound

end QuantitativeMaass.IntegralSchur

#print axioms QuantitativeMaass.IntegralSchur.energy_integrable
