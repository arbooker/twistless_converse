module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticL2Multiplier

open MeasureTheory Filter ContinuousLinearMap
open scoped InnerProduct

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Multiplication by a bounded measurable scalar function preserves L². -/
theorem memLp_mul (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) (f : Lp ℂ 2 μ) : MemLp (fun x => c x*f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c:=C) (hc.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  change ‖c x*f x‖≤C*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

noncomputable def linear (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_mul c hc hC f).toLp (fun x => c x*f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul c hc hC (f+g)),
      MemLp.coeFn_toLp (memLp_mul c hc hC f),MemLp.coeFn_toLp (memLp_mul c hc hC g),
      Lp.coeFn_add f g,Lp.coeFn_add ((memLp_mul c hc hC f).toLp _) ((memLp_mul c hc hC g).toLp _)] with x hfg hf hg ha hb
    simp only [hfg,hf,hg,ha,hb,Pi.add_apply,mul_add]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul c hc hC (z • f)),
      MemLp.coeFn_toLp (memLp_mul c hc hC f),Lp.coeFn_smul z f,
      Lp.coeFn_smul z ((memLp_mul c hc hC f).toLp _)] with x hz hf ha hb
    simp only [RingHom.id_apply,hz,hf,ha,hb,Pi.smul_apply,smul_eq_mul]
    ring

theorem linear_coeFn (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) (f : Lp ℂ 2 μ) : linear c hc hC f =ᵐ[μ] (fun x => c x*f x) :=
  MemLp.coeFn_toLp (memLp_mul c hc hC f)

theorem linear_norm_le (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) (f : Lp ℂ 2 μ) : ‖linear c hc hC f‖≤C*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [linear_coeFn c hc hC f,hC] with x hx hcx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hcx (norm_nonneg _)

noncomputable def operator (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linear c hc hC).mkContinuous C (linear_norm_le c hc hC)

theorem operator_coeFn (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) (f : Lp ℂ 2 μ) : operator c hc hC f =ᵐ[μ] (fun x => c x*f x) :=
  linear_coeFn c hc hC f

theorem operator_norm_le (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC0 : 0≤C) (hC : ∀ᵐ x ∂μ,‖c x‖≤C) : ‖operator c hc hC‖≤C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0 (linear_norm_le c hc hC)

/-- A real multiplier is self-adjoint on the actual L² space. -/
theorem operator_adjoint (c : α → ℂ) (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ,‖c x‖≤C) (hreal : ∀ᵐ x ∂μ,star (c x)=c x) :
    (operator c hc hC).adjoint=operator c hc hC := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_coeFn c hc hC f,operator_coeFn c hc hC g,hreal] with x hf hg hr
  simp only [hf,hg,RCLike.inner_apply]
  change g x*star (c x*f x)=(c x*g x)*star (f x)
  rw [star_mul,hr]
  ring

/-- The squared Hilbert norm is the integral of the pointwise squared norm. -/
theorem norm_sq_eq_integral (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜:=ℂ),L2.inner_def,← integral_re (L2.integrable_inner f f)]
  congr 1
  ext x
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (f x)

#print axioms operator_adjoint
#print axioms norm_sq_eq_integral

end AsymptoticL2Multiplier
