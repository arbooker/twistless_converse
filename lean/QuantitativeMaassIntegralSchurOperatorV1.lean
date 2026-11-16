module

public import QuantitativeMaassIntegralSchurL2V1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass.IntegralSchur
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SFinite μ]

def Data.toLp (D : Data μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (D.output_memLp f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp (D.output f)

theorem Data.toLp_coeFn (D : Data μ) (f : Lp ℂ 2 μ) :
    D.toLp f =ᵐ[μ] D.output f := MemLp.coeFn_toLp _

omit [SFinite μ] in
theorem Data.output_congr_ae (D : Data μ) {f g : A → ℂ} (h : f=ᵐ[μ] g) :
    D.output f=D.output g := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem Data.output_add_ae (D : Data μ) (f g : Lp ℂ 2 μ) :
    D.output ((f+g : Lp ℂ 2 μ) : A → ℂ)=ᵐ[μ] (fun x => D.output f x+D.output g x) := by
  have he := D.output_congr_ae (Lp.coeFn_add f g)
  rw [he]
  filter_upwards [D.output_row_ae f (Lp.stronglyMeasurable f).measurable (Lp.memLp f),
    D.output_row_ae g (Lp.stronglyMeasurable g).measurable (Lp.memLp g)] with x hf hg
  change (∫ y,D.kernel x y*(f y+g y) ∂μ)=_
  simp_rw [mul_add]
  exact integral_add hf.1 hg.1

omit [SFinite μ] in
theorem Data.output_smul (D : Data μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    D.output ((c • f : Lp ℂ 2 μ) : A → ℂ)=(fun x => c*D.output f x) := by
  rw [D.output_congr_ae (Lp.coeFn_smul c f)]
  funext x
  change (∫ y,D.kernel x y*(c*f y) ∂μ)=c*∫ y,D.kernel x y*f y ∂μ
  simp_rw [mul_left_comm (D.kernel x _) c]
  exact integral_const_mul c _

/-- The integral formula descends to genuine almost-everywhere L2 classes. -/
def Data.linear (D : Data μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := D.toLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [D.toLp_coeFn (f+g),D.toLp_coeFn f,D.toLp_coeFn g,
      Lp.coeFn_add (D.toLp f) (D.toLp g),D.output_add_ae f g] with x hfg hf hg ha hs
    simp only [hfg,ha,Pi.add_apply,hf,hg,hs]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [D.toLp_coeFn (c • f),D.toLp_coeFn f,
      Lp.coeFn_smul c (D.toLp f)] with x hcf hf hs
    simp only [RingHom.id_apply,hcf,hs,Pi.smul_apply,hf,D.output_smul,smul_eq_mul]

theorem Data.linear_norm (D : Data μ) (f : Lp ℂ 2 μ) :
    ‖D.linear f‖≤D.bound*‖f‖ := by
  change ‖D.toLp f‖≤D.bound*‖f‖
  have he : ‖D.toLp f‖^2=∫ x,‖D.output f x‖^2 ∂μ := by
    rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [D.toLp_coeFn f] with x hx
    rw [hx]
  have h := D.output_energy f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  rw [← he,← AsymptoticL2Multiplier.norm_sq_eq_integral] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg D.bound_nonneg (norm_nonneg _))).mp
  simpa only [mul_pow] using h

/-- A bounded operator constructed from the actual integral kernel, with
the uniform row/column bound as its operator norm estimate. -/
def Data.operator (D : Data μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  D.linear.mkContinuous D.bound D.linear_norm

theorem Data.operator_coeFn (D : Data μ) (f : Lp ℂ 2 μ) :
    D.operator f=ᵐ[μ] (fun x => ∫ y,D.kernel x y*f y ∂μ) := D.toLp_coeFn f

theorem Data.operator_norm (D : Data μ) : ‖D.operator‖≤D.bound :=
  ContinuousLinearMap.opNorm_le_bound _ D.bound_nonneg D.linear_norm

#print axioms Data.linear
#print axioms Data.operator_coeFn
#print axioms Data.operator_norm

end QuantitativeMaass.IntegralSchur
