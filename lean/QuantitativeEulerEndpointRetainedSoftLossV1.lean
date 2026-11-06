module

public import QuantitativeEulerEndpointSoftTraceLossV1
public import QuantitativeEulerEndpointRetainedSharpeningV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSoftUpdate
open Polynomial MeasureTheory

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- One polynomial block update has a verified spectral trace-loss bound,
small outgoing idempotency defect and exact solution preservation, with
explicit sharpening degree and coefficient mass. The input high spectral
mass is the ACTUAL measure of C, not an assumed contraction. -/
theorem exists_sharpened_update_with_loss_scalar (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (hcyc : ∀ a b : 𝔄, τ (a*b)=τ (b*a))
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hCA : C≤A^2)
    (d : ℕ) (lam : ℝ) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ i∈p.support, |p.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      QuantitativeEulerEndpointBernstein.ScalarSharpening p ∧
      0≤aeval (update A C d) p ∧ aeval (update A C d) p≤A ∧
      τ (aeval (update A C d) p-(aeval (update A C d) p)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, A*E=E → C*E=0 → aeval (update A C d) p*E=E) ∧
      (1-Real.exp (-(d:ℝ)*lam)) *
        (QuantitativeTracialSpectralMeasure.measure τ hτ C (IsSelfAdjoint.of_nonneg hC0)).real
          {x : spectrum ℝ C | lam≤(x:ℝ)} - 2*(d:ℝ)*τ (A-A^2) ≤
        τ A-τ (aeval (update A C d) p) := by
  have hAA := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  have hC1 : C≤1 := hCA.trans (by simpa only [pow_two] using hAA.trans hA1)
  have ho := update_order A C hA0 hA1 hC0 hC1 d
  obtain ⟨p,hdeg,hmass,hscalar,hp0,hp1,hdef⟩ :=
    QuantitativeEulerEndpointBernstein.exists_controlled_operator_sharpening_scalar τ hτ
      (update A C d) ho.1 (ho.2.trans hA1) hJ
  refine ⟨p,hdeg,hmass,hscalar,hp0,hp1.trans ho.2,hdef,?_,?_⟩
  · intro E hAE hCE
    exact QuantitativeEulerEndpointBernstein.polynomial_preserves_fixed _ E
      (update_fixed A C E hAE hCE d) p hscalar.2.1
  · exact (update_trace_loss τ hτ hcyc A C hA0 hA1 hC0 hCA d lam).trans
      (sub_le_sub_left (hτ hp1) _)

#print axioms exists_sharpened_update_with_loss_scalar
end QuantitativeEulerEndpointSoftUpdate
