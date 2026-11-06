module

public import QuantitativeEulerEndpointSoftUpdateV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTracialProduct
open Polynomial

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
  (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ) (hcyc : ∀ a b : 𝔄, τ (a*b)=τ (b*a))

include hcyc in
theorem trace_product_sqrt (X Y : 𝔄) (hX : 0≤X) :
    τ (X*Y)=τ (CFC.sqrt X*Y*CFC.sqrt X) := by
  have h := hcyc (CFC.sqrt X) (CFC.sqrt X*Y)
  rwa [← mul_assoc,CFC.sqrt_mul_sqrt_self X hX] at h

include hτ hcyc in
theorem trace_product_nonneg (X Y : 𝔄) (hX : 0≤X) (hY : 0≤Y) : 0≤τ (X*Y) := by
  rw [trace_product_sqrt τ hcyc X Y hX]
  simpa only [map_zero] using hτ (conjugate_nonneg_of_nonneg hY (CFC.sqrt_nonneg X))

include hτ hcyc in
theorem trace_product_mono (X Y Z : 𝔄) (hX : 0≤X) (hYZ : Y≤Z) : τ (X*Y)≤τ (X*Z) := by
  rw [trace_product_sqrt τ hcyc X Y hX,trace_product_sqrt τ hcyc X Z hX]
  exact hτ (conjugate_le_conjugate_of_nonneg hYZ (CFC.sqrt_nonneg X))

/-- Scalar CFC inequality controlling the price of replacing a projection
by a positive contraction. -/
theorem defect_product_le (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) :
    (1-A^2)*A^2≤(2:ℝ) • (A-A^2) := by
  have hA := IsSelfAdjoint.of_nonneg hA0
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1
  have hh := cfc_mono (a := A)
    (f := (((1-X^2)*X^2 : ℝ[X])).eval) (g := ((C 2*(X-X^2) : ℝ[X])).eval) (fun x hx => by
      have hx0 : 0≤x := spectrum_nonneg_of_nonneg hA0 hx
      have hx1 : x≤1 := (le_abs_self x).trans ((quasispectrum.norm_le_norm_of_mem
        (spectrum_subset_quasispectrum ℝ A hx)).trans hn)
      simp only [eval_mul,eval_sub,eval_one,eval_pow,eval_X,eval_C]
      have hpos := mul_nonneg (mul_nonneg hx0 (sq_nonneg (1-x))) (by linarith : 0≤x+2)
      nlinarith only [hpos])
  simpa only [cfc_polynomial _ A hA,map_mul,map_sub,map_one,map_pow,aeval_X,aeval_C,
    ← Algebra.smul_def] using hh

include hτ hcyc in
/-- Trace loss of sandwiching a filter by a near projection. The error is
proportional to its actual idempotency defect. -/
theorem sandwich_trace_lower (A F : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    {d : ℝ} (hd : 0≤d) (hF : F≤d • A^2) :
    τ F-2*d*τ (A-A^2)≤τ (A*F*A) := by
  have hAA := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  have hsq : A^2≤1 := by simpa only [pow_two] using hAA.trans hA1
  have hm := trace_product_mono τ hτ hcyc (1-A^2) F (d • A^2) (sub_nonneg.mpr hsq) hF
  rw [mul_smul_comm,map_smul,smul_eq_mul] at hm
  have hb := mul_le_mul_of_nonneg_left (hτ (defect_product_le A hA0 hA1)) hd
  rw [map_smul,smul_eq_mul] at hb
  have he : τ ((1-A^2)*F)=τ F-τ (A*F*A) := by
    rw [sub_mul,one_mul,map_sub]
    have hc := hcyc A (A*F)
    rw [← mul_assoc,← pow_two] at hc
    rw [hc]
  rw [he] at hm
  linarith

#print axioms trace_product_sqrt
#print axioms trace_product_nonneg
#print axioms trace_product_mono
#print axioms defect_product_le
#print axioms sandwich_trace_lower
end QuantitativeEulerEndpointTracialProduct
