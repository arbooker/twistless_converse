module

public import QuantitativeEulerEndpointAmplifierV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSoftUpdate
open Polynomial MeasureTheory

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- The actual compressed and normalized residual energy is bounded by
A squared, the stronger estimate needed for the trace-loss error. -/
theorem compressed_energy_le_square (A G : 𝔄) (hA0 : 0≤A)
    {K : ℝ} (hK : 0<K) (hGK : G≤K • (1:𝔄)) : K⁻¹ • (A*G*A)≤A^2 := by
  have hc := (IsSelfAdjoint.of_nonneg hA0).conjugate_le_conjugate hGK
  have he : A*(K • (1:𝔄))*A=K • A^2 := by simp only [mul_smul_comm,smul_mul_assoc,mul_one,pow_two]
  rw [he] at hc
  have hh := smul_le_smul_of_nonneg_left hc (inv_nonneg.mpr hK.le)
  simpa only [smul_smul,inv_mul_cancel₀ hK.ne',one_smul] using hh

theorem update_trace_loss (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (hcyc : ∀ a b : 𝔄, τ (a*b)=τ (b*a))
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hCA : C≤A^2)
    (d : ℕ) (lam : ℝ) :
    (1-Real.exp (-(d:ℝ)*lam)) *
      (QuantitativeTracialSpectralMeasure.measure τ hτ C (IsSelfAdjoint.of_nonneg hC0)).real
        {x : spectrum ℝ C | lam≤(x:ℝ)} - 2*(d:ℝ)*τ (A-A^2) ≤
      τ A-τ (update A C d) := by
  have hAA := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  have hC1 : C≤1 := hCA.trans (by simpa only [pow_two] using hAA.trans hA1)
  have hF := (amplifier_le_linear C hC0 hC1 d).trans
    (smul_le_smul_of_nonneg_left hCA (Nat.cast_nonneg d))
  have hs := QuantitativeEulerEndpointTracialProduct.sandwich_trace_lower τ hτ hcyc
    A (amplifier C d) hA0 hA1 (Nat.cast_nonneg d) hF
  have hh := amplifier_trace_lower τ hτ C hC0 hC1 d lam
  rw [amplifier_eq] at hs hh
  simp only [update,map_sub] at hs hh ⊢
  linarith

/-- One polynomial block update has a verified spectral trace-loss bound,
small outgoing idempotency defect and exact solution preservation, with
explicit sharpening degree and coefficient mass. The input high spectral
mass is the ACTUAL measure of C, not an assumed contraction. -/
theorem exists_sharpened_update_with_loss (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (hcyc : ∀ a b : 𝔄, τ (a*b)=τ (b*a))
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hCA : C≤A^2)
    (d : ℕ) (lam : ℝ) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ i∈p.support, |p.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
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
  obtain ⟨p,hdeg,hmass,_hzero,hone,hp0,hp1,hdef⟩ :=
    QuantitativeEulerEndpointBernstein.exists_controlled_operator_sharpening τ hτ
      (update A C d) ho.1 (ho.2.trans hA1) hJ
  refine ⟨p,hdeg,hmass,hp0,hp1.trans ho.2,hdef,?_,?_⟩
  · intro E hAE hCE
    exact QuantitativeEulerEndpointBernstein.polynomial_preserves_fixed _ E
      (update_fixed A C E hAE hCE d) p hone
  · exact (update_trace_loss τ hτ hcyc A C hA0 hA1 hC0 hCA d lam).trans
      (sub_le_sub_left (hτ hp1) _)

#print axioms compressed_energy_le_square
#print axioms update_trace_loss
#print axioms exists_sharpened_update_with_loss
end QuantitativeEulerEndpointSoftUpdate
