module

public import AsymptoticRegularSignedTraceV1
public import AsymptoticOrbitDiagonalV1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Set ContinuousLinearMap AsymptoticOrbitDiagonal
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]

omit [MeasurableSpace α] in
theorem root_norm_le_corner {s : Set α}
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hB : ∀ x,‖B x‖≤C) (hsupport : ∀ x,(B x).comp (corner s x)=B x) (x : α) :
    ‖(matrix (B x) 1 1).re‖≤s.indicator (fun _ => C) x := by
  classical
  by_cases hx : x∈s
  · rw [Set.indicator_of_mem hx,Real.norm_eq_abs]
    apply (Complex.abs_re_le_norm _).trans
    calc
      ‖matrix (B x) 1 1‖≤‖B x‖*‖delta (1:G)‖ :=
        (lp.norm_apply_le_norm (by norm_num) (B x (delta 1)) 1).trans ((B x).le_opNorm _)
      _ ≤ C := by simpa only [root_delta_norm,mul_one] using hB x
  · have he := congrArg (fun T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => T (delta 1)) (hsupport x)
    rw [comp_apply,corner_delta,one_smul,ite_eq_right hx,map_zero] at he
    simp [matrix,← he,hx]

theorem corner_diagonal_integrable (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (hf : μ s<∞)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hm : Measurable (fun x => matrix (B x) 1 1))
    (hB : ∀ x,‖B x‖≤C) (hsupport : ∀ x,(B x).comp (corner s x)=B x) :
    Integrable (fun x => (matrix (B x) 1 1).re) μ := by
  have hi : Integrable (s.indicator (fun _ : α => C)) μ :=
    (integrableOn_const hf.ne).integrable_indicator hs
  exact hi.mono' (Complex.continuous_re.measurable.comp hm).aestronglyMeasurable
    (Filter.Eventually.of_forall (root_norm_le_corner B hB hsupport))

theorem norm_signedTrace_le_corner (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (hf : μ s<∞)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hB : ∀ x,‖B x‖≤C) (hsupport : ∀ x,(B x).comp (corner s x)=B x) :
    ‖signedTrace μ B‖≤C*(μ s).toReal := by
  have hi : Integrable (s.indicator (fun _ : α => C)) μ :=
    (integrableOn_const hf.ne).integrable_indicator hs
  apply (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (root_norm_le_corner B hB hsupport))).trans_eq
  rw [integral_indicator_const _ hs]
  simp only [smul_eq_mul,measureReal_def,mul_comm]

#print axioms corner_diagonal_integrable
#print axioms norm_signedTrace_le_corner

end AsymptoticRegularTrace
