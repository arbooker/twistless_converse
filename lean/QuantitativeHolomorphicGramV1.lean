module

public import QuantitativeHolomorphicNewtonV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

def inverseSqrtCFC (A : 𝔄) : 𝔄 := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

theorem inverseSqrt_continuousOn {κ : ℝ} (hκ : 0 < κ) (A : 𝔄)
    (hlo : ∀ x ∈ spectrum ℝ A, κ ≤ x) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ A) :=
  Real.continuous_sqrt.continuousOn.inv₀
    (fun x hx => (Real.sqrt_pos.2 (hκ.trans_le (hlo x hx))).ne')

/-- Explicit polynomial approximation in the actual C*-algebra norm. -/
theorem inverseSqrt_polynomial_norm_error {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (A : 𝔄) (hA : IsSelfAdjoint A)
    (hspec : ∀ x ∈ spectrum ℝ A, κ ≤ x ∧ x ≤ 1) (n : ℕ) :
    ‖Polynomial.aeval A (inverseSqrtPolynomial n) - inverseSqrtCFC A‖ ≤
      (1 - κ) ^ (2 ^ n) / Real.sqrt κ := by
  have hf := inverseSqrt_continuousOn hκ A (fun x hx => (hspec x hx).1)
  rw [inverseSqrtCFC, ← cfc_polynomial (inverseSqrtPolynomial n) A hA,
    ← cfc_sub (inverseSqrtPolynomial n).eval (fun x : ℝ => (Real.sqrt x)⁻¹) A
      (inverseSqrtPolynomial n).continuous.continuousOn hf]
  apply norm_cfc_le (div_nonneg (pow_nonneg (sub_nonneg.mpr hκ1) _) (Real.sqrt_nonneg κ))
  intro x hx
  simpa only [Real.norm_eq_abs, inverseSqrtValue] using
    inverseSqrt_uniform_scalar_error hκ (hspec x hx).1 (hspec x hx).2 n

theorem inverseSqrtCFC_selfAdjoint (A : 𝔄) : IsSelfAdjoint (inverseSqrtCFC A) :=
  cfc_predicate _ _

/-- The exact CFC normalizer really cancels the positive Gram operator. -/
theorem inverseSqrtCFC_normalizes {κ : ℝ} (hκ : 0 < κ) (A : 𝔄)
    (hA : IsSelfAdjoint A) (hlo : ∀ x ∈ spectrum ℝ A, κ ≤ x) :
    inverseSqrtCFC A * A * inverseSqrtCFC A = 1 := by
  have hf := inverseSqrt_continuousOn hκ A hlo
  have hid : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := continuous_id.continuousOn
  calc
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) A := by
      rw [cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹ * x)
        (fun x : ℝ => (Real.sqrt x)⁻¹) A (hf.mul hid) hf,
        cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) A hf hid,
        cfc_id' ℝ A hA]
      rfl
    _ = cfc (fun _ : ℝ => 1) A := by
      apply cfc_congr
      intro x hx
      have hx0 : 0 < x := hκ.trans_le (hlo x hx)
      have hsq := Real.sq_sqrt hx0.le
      have hs := (Real.sqrt_pos.2 hx0).ne'
      field_simp
      nlinarith only [hsq]
    _ = 1 := cfc_const_one ℝ A hA

section HilbertSpace

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The lower Gram bound follows from the actual reconstruction energy. -/
theorem reconstruction_gram_lower (R : G →L[ℂ] H) {κ : ℝ}
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) :
    algebraMap ℝ (G →L[ℂ] G) κ ≤ R.adjoint.comp R := by
  rw [ContinuousLinearMap.le_def]
  refine ContinuousLinearMap.isPositive_def'.2 ⟨
    (isPositive_adjoint_comp_self R).isSelfAdjoint.sub
      (cfc_predicate_algebraMap (R := ℝ) κ), ?_⟩
  intro v
  have he : (⟪(R.adjoint.comp R - algebraMap ℝ (G →L[ℂ] G) κ) v, v⟫_ℂ).re =
      ‖R v‖ ^ 2 - κ * ‖v‖ ^ 2 := by
    simp only [sub_apply, comp_apply, ContinuousLinearMap.algebraMap_apply,
      inner_sub_left, adjoint_inner_left, Complex.sub_re]
    rw [inner_smul_left_eq_smul]
    simp only [inner_self_eq_norm_sq_to_K, Complex.smul_re, smul_eq_mul]
    norm_cast
  change 0 ≤ (⟪(R.adjoint.comp R - algebraMap ℝ (G →L[ℂ] G) κ) v, v⟫_ℂ).re
  rw [he]
  exact sub_nonneg.mpr (hR v)

/-- The spectrum interval required by Newton's method is derived from
energy and norm bounds on the actual reconstruction map. -/
theorem reconstruction_gram_spectrum (R : G →L[ℂ] H) {κ : ℝ}
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) (hRn : ‖R‖ ≤ 1) :
    ∀ x ∈ spectrum ℝ (R.adjoint.comp R), κ ≤ x ∧ x ≤ 1 := by
  have hSA := (isPositive_adjoint_comp_self R).isSelfAdjoint
  have hlo := (algebraMap_le_iff_le_spectrum hSA).1 (reconstruction_gram_lower R hR)
  have hn : ‖R.adjoint.comp R‖ ≤ 1 := by
    rw [norm_adjoint_comp_self]
    simpa only [one_mul] using mul_le_mul hRn hRn (norm_nonneg R) zero_le_one
  have hpos : 0 ≤ R.adjoint.comp R :=
    ContinuousLinearMap.nonneg_iff_isPositive.2 (isPositive_adjoint_comp_self R)
  have hupper := (CFC.le_one_iff (R := ℝ) (R.adjoint.comp R) hSA).1
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).1 hn)
  intro x hx
  exact ⟨hlo x hx, hupper x hx⟩

/-- Exact normalized reconstruction and its finite polynomial version. -/
def normalizedReconstruction (R : G →L[ℂ] H) : G →L[ℂ] H :=
  R.comp (inverseSqrtCFC (R.adjoint.comp R))

def polynomialNormalizedReconstruction (R : G →L[ℂ] H) (n : ℕ) : G →L[ℂ] H :=
  R.comp (Polynomial.aeval (R.adjoint.comp R) (inverseSqrtPolynomial n))

theorem normalizedReconstruction_gram (R : G →L[ℂ] H) {κ : ℝ} (hκ : 0 < κ)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) :
    (normalizedReconstruction R).adjoint.comp (normalizedReconstruction R) = 1 := by
  have hSA := (isPositive_adjoint_comp_self R).isSelfAdjoint
  have hlo := (algebraMap_le_iff_le_spectrum hSA).1 (reconstruction_gram_lower R hR)
  have he := inverseSqrtCFC_normalizes hκ (R.adjoint.comp R) hSA hlo
  have hh := inverseSqrtCFC_selfAdjoint (R.adjoint.comp R)
  change (inverseSqrtCFC (R.adjoint.comp R)).adjoint = _ at hh
  simpa only [normalizedReconstruction, adjoint_comp, hh, mul_def, comp_assoc] using he

theorem normalizedReconstruction_norm (R : G →L[ℂ] H) {κ : ℝ} (hκ : 0 < κ)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) (v : G) :
    ‖normalizedReconstruction R v‖ = ‖v‖ := by
  exact (norm_map_iff_adjoint_comp_self (normalizedReconstruction R)).2
    (normalizedReconstruction_gram R hκ hR) v

/-- An explicit coordinate change reconstructs every vector in the old
range, so normalization loses no actual solution. -/
theorem normalizedReconstruction_reconstruct (R : G →L[ℂ] H) {κ : ℝ} (hκ : 0 < κ)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) (v : G) :
    normalizedReconstruction R
      ((R.adjoint.comp R).comp (inverseSqrtCFC (R.adjoint.comp R)) v) = R v := by
  have hSA := (isPositive_adjoint_comp_self R).isSelfAdjoint
  have hlo := (algebraMap_le_iff_le_spectrum hSA).1 (reconstruction_gram_lower R hR)
  have he := inverseSqrtCFC_normalizes hκ (R.adjoint.comp R) hSA hlo
  have hv := congrArg (fun T : G →L[ℂ] G => T v) he
  simp only [mul_def, comp_apply, one_apply_eq_self] at hv
  change R ((inverseSqrtCFC (R.adjoint.comp R))
    ((R.adjoint.comp R) ((inverseSqrtCFC (R.adjoint.comp R)) v))) = R v
  simpa only [comp_apply] using congrArg R hv

omit [CompleteSpace G] [CompleteSpace H] in
/-- Scaling a norm-dominating reconstruction gives the actual hypotheses
for the Gram interval; no spectral bounds are assumed. -/
theorem scaled_reconstruction_bounds (R : G →L[ℂ] H) {B : ℝ} (hB : 0 < B)
    (hRn : ‖R‖ ≤ B) (hR : ∀ v, ‖v‖ ≤ ‖R v‖) :
    ‖(B⁻¹ : ℝ) • R‖ ≤ 1 ∧
      ∀ v, (B⁻¹) ^ 2 * ‖v‖ ^ 2 ≤ ‖((B⁻¹ : ℝ) • R) v‖ ^ 2 := by
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hB)]
    exact (mul_le_mul_of_nonneg_left hRn (inv_nonneg.mpr hB.le)).trans_eq
      (inv_mul_cancel₀ hB.ne')
  · intro v
    rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hB), mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) (hR v) 2)
      (sq_nonneg _)

omit [CompleteSpace G] [CompleteSpace H] in
/-- A proved operator bound gives a scalar-normalized contraction. -/
theorem scaled_norm_le_one (R : G →L[ℂ] H) {B : ℝ} (hB : 0 < B)
    (hR : ‖R‖ ≤ B) : ‖(B⁻¹ : ℝ) • R‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hB)]
  exact (mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hB.le)).trans_eq
    (inv_mul_cancel₀ hB.ne')

omit [CompleteSpace G] [CompleteSpace H] in
/-- Scalar contraction preserves an explicit operator approximation error. -/
theorem scaled_difference_norm_le (R V : G →L[ℂ] H) {c δ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (herr : ‖V - R‖ ≤ δ) :
    ‖c • V - c • R‖ ≤ δ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans
    (by simpa only [one_mul] using herr)

/-- No normalization error is assumed: it is proved by CFC from the
explicit scalar Newton residual. -/
theorem polynomialNormalizedReconstruction_error (R : G →L[ℂ] H) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2) (hRn : ‖R‖ ≤ 1) (n : ℕ) :
    ‖polynomialNormalizedReconstruction R n - normalizedReconstruction R‖ ≤
      (1 - κ) ^ (2 ^ n) / Real.sqrt κ := by
  have he := inverseSqrt_polynomial_norm_error hκ hκ1 (R.adjoint.comp R)
    (isPositive_adjoint_comp_self R).isSelfAdjoint (reconstruction_gram_spectrum R hR hRn) n
  rw [polynomialNormalizedReconstruction, normalizedReconstruction, ← comp_sub]
  apply (opNorm_comp_le _ _).trans
  exact (mul_le_mul hRn he (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end HilbertSpace

#print axioms reconstruction_gram_spectrum
#print axioms normalizedReconstruction_gram
#print axioms normalizedReconstruction_norm
#print axioms normalizedReconstruction_reconstruct
#print axioms scaled_reconstruction_bounds
#print axioms polynomialNormalizedReconstruction_error

#print axioms inverseSqrt_polynomial_norm_error
#print axioms inverseSqrtCFC_normalizes

end QuantitativeHolomorphic
