module

public import QuantitativeMaassIntegralSchurEnergyV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass.IntegralSchur
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SFinite μ]

/-- Concrete measurable integral-kernel data. The actual hyperbolic kernel
will supply all these estimates from geometric unfolding. -/
structure Data (μ : Measure A) where
  kernel : A → A → ℂ
  measurable : Measurable (Function.uncurry kernel)
  bound : ℝ
  bound_nonneg : 0≤bound
  row_integrable : ∀ x,Integrable (kernel x) μ
  column_integrable : ∀ y,Integrable (fun x => kernel x y) μ
  row_bound : ∀ x,(∫ y,‖kernel x y‖ ∂μ)≤bound
  column_bound : ∀ y,(∫ x,‖kernel x y‖ ∂μ)≤bound

def Data.output (D : Data μ) (f : A → ℂ) (x : A) : ℂ := ∫ y,D.kernel x y*f y ∂μ

theorem Data.output_measurable (D : Data μ) (f : A → ℂ) (hf : Measurable f) :
    Measurable (D.output f) :=
  (D.measurable.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

/-- The row integrals are absolutely convergent almost everywhere and
satisfy the pointwise weighted-square estimate. -/
theorem Data.output_row_ae (D : Data μ) (f : A → ℂ) (hf : Measurable f) (hL : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => D.kernel x y*f y) μ ∧
      ‖D.output f x‖^2≤D.bound*(∫ y,‖D.kernel x y‖*‖f y‖^2 ∂μ) := by
  have hE := (energy_integrable D.kernel D.measurable D.bound_nonneg
    D.column_integrable D.column_bound f hf hL).1
  filter_upwards [hE.prod_right_ae] with x hx
  have h := IntegralSchur.row_bound (D.kernel x) f
    (D.measurable.comp (measurable_const.prodMk measurable_id)) hf (D.row_integrable x) hx
  refine ⟨h.1,h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (D.row_bound x)
    (integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

/-- Schur's test proves that the literal integral output is in L2. -/
theorem Data.output_memLp (D : Data μ) (f : A → ℂ) (hf : Measurable f) (hL : MemLp f 2 μ) :
    MemLp (D.output f) 2 μ := by
  have hE := (energy_integrable D.kernel D.measurable D.bound_nonneg
    D.column_integrable D.column_bound f hf hL).1
  apply (memLp_two_iff_integrable_sq_norm (D.output_measurable f hf).aestronglyMeasurable).mpr
  apply (hE.integral_prod_left.const_mul D.bound).mono'
    ((D.output_measurable f hf).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [D.output_row_ae f hf hL] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hx.2

/-- The full square norm bound, including both integral interchanges. -/
theorem Data.output_energy (D : Data μ) (f : A → ℂ) (hf : Measurable f) (hL : MemLp f 2 μ) :
    (∫ x,‖D.output f x‖^2 ∂μ)≤D.bound^2*(∫ y,‖f y‖^2 ∂μ) := by
  have hE := energy_integrable D.kernel D.measurable D.bound_nonneg
    D.column_integrable D.column_bound f hf hL
  have ho := (D.output_memLp f hf hL).norm.integrable_sq
  calc
    _ ≤ ∫ x,D.bound*(∫ y,‖D.kernel x y‖*‖f y‖^2 ∂μ) ∂μ :=
      integral_mono_ae ho (hE.1.integral_prod_left.const_mul D.bound)
        ((D.output_row_ae f hf hL).mono fun _ h => h.2)
    _ = D.bound*(∫ p : A×A,‖D.kernel p.1 p.2‖*‖f p.2‖^2 ∂μ.prod μ) := by
      rw [integral_const_mul,integral_prod _ hE.1]
    _ ≤ D.bound*(D.bound*(∫ y,‖f y‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hE.2 D.bound_nonneg
    _ = _ := by ring

#print axioms Data.output_row_ae
#print axioms Data.output_memLp
#print axioms Data.output_energy

end QuantitativeMaass.IntegralSchur
