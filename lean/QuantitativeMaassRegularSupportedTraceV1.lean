module

public import AsymptoticRegularBoundedSandwichV1
public import QuantitativeMaassWeightedProjectionExcessV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α]

/-- A bounded weight in a finite-energy sandwich pays only the finite Gram
trace. No finite-trace assumption on the ambient identity is required. -/
theorem signedTrace_adjoint_sandwich_bound (μ : Measure α)
    (R B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hR : ∀ g h,Measurable (fun x => matrix (R x) g h))
    (hf : trace μ (fun x => (R x).adjoint.comp (R x))<∞)
    {C : ℝ} (hB : ∀ x,‖B x‖≤C) :
    |signedTrace μ (fun x => (R x).adjoint.comp ((B x).comp (R x)))|≤
      C*(trace μ (fun x => (R x).adjoint.comp (R x))).toReal := by
  have hi := (energy_integrable μ R hR hf).const_mul C
  have hb (x : α) : |(matrix ((R x).adjoint.comp ((B x).comp (R x))) 1 1).re|≤
      C*‖R x (delta 1)‖^2 := by
    rw [matrix_cross]
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_inner_le_norm _ _).trans
    have hh := mul_le_mul_of_nonneg_left ((B x).le_of_opNorm_le (hB x) (R x (delta 1)))
      (norm_nonneg (R x (delta 1)))
    simpa only [comp_apply] using hh.trans_eq (by ring)
  calc
    _ ≤ ∫ x,|(matrix ((R x).adjoint.comp ((B x).comp (R x))) 1 1).re| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x,C*‖R x (delta 1)‖^2 ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hi
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul,energy_integral_eq_toReal μ R hR]

variable [MulAction G α]

/-- The actual semifinite regular trace bound for a right-supported error.
Cyclicity first compresses the error to its finite canonical projection. -/
theorem signedTrace_right_supported_bound (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (E B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hE : ∀ x,IsStarProjection (E x))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcE : Covariant E) (hcB : Covariant B)
    (hf : trace μ E<∞) {C : ℝ} (hb : ∀ x,‖B x‖≤C)
    (hs : ∀ x,(B x)*(E x)=B x) :
    |signedTrace μ B|≤C*(trace μ E).toReal := by
  have ha (x : α) : (E x).adjoint=E x := by
    rw [←ContinuousLinearMap.star_eq_adjoint]
    exact (hE x).isSelfAdjoint.star_eq
  have he (x : α) : (E x).adjoint.comp (E x)=E x := by
    rw [ha]
    exact (hE x).isIdempotentElem.eq
  have hfg : trace μ (fun x => (E x).adjoint.comp (E x))<∞ := by
    simpa only [he] using hf
  have ht := signedTrace_bounded_sandwich μ hmp E B hmE hmB hcE hcB hfg hb
  have hh := signedTrace_adjoint_sandwich_bound μ E B hmE hfg hb
  simp only [he] at ht hh
  have hleft : (fun x => (E x).comp ((B x).comp (E x).adjoint))=
      (fun x => (E x).adjoint.comp ((B x).comp (E x))) := by
    funext x
    rw [ha]
  rw [hleft] at ht
  have hright : (fun x => (B x).comp (E x))=B := by
    funext x
    exact hs x
  rw [hright] at ht
  rw [ht] at hh
  exact hh

#print axioms signedTrace_adjoint_sandwich_bound
#print axioms signedTrace_right_supported_bound
end AsymptoticRegularTrace
