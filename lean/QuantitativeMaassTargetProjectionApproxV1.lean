module

public import QuantitativeMaassWeightedTargetProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap QuantitativeHolomorphic

namespace QuantitativeMaass

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator approximation to an isometry gives a quantitative
approximation to its range projection. -/
theorem cogram_error_of_isometry_approx (A U : V →L[ℂ] H) (hU : ‖U‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (he : ‖A-U‖≤δ) :
    ‖A.comp A.adjoint-U.comp U.adjoint‖≤δ*(2+δ) := by
  have hA : ‖A‖≤1+δ := by
    calc
      ‖A‖=‖(A-U)+U‖ := by rw [sub_add_cancel]
      _ ≤ ‖A-U‖+‖U‖ := norm_add_le _ _
      _ ≤ δ+1 := add_le_add he hU
      _ = 1+δ := add_comm _ _
  have hid : A.comp A.adjoint-U.comp U.adjoint=
      (A-U).comp A.adjoint+U.comp (A-U).adjoint := by
    rw [map_sub,sub_comp,comp_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(A-U).comp A.adjoint‖+‖U.comp (A-U).adjoint‖ := norm_add_le _ _
    _ ≤ ‖A-U‖*‖A.adjoint‖+‖U‖*‖(A-U).adjoint‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = ‖A-U‖*‖A‖+‖U‖*‖A-U‖ := by rw [adjoint.norm_map,adjoint.norm_map]
    _ ≤ δ*(1+δ)+1*δ := add_le_add
      (mul_le_mul he hA (norm_nonneg _) hδ)
      (mul_le_mul hU he (norm_nonneg _) zero_le_one)
    _ = δ*(2+δ) := by ring

/-- An explicit finite polynomial in the compressed Gram operator
approximates the actual orthogonal range projection. -/
theorem polynomial_embedding_projection_error (R : V →L[ℂ] H) [CompleteSpace R.range]
    {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (hR : ∀ x,κ*‖x‖^2≤‖R x‖^2) (hRn : ‖R‖≤1) (n : ℕ) :
    ‖(polynomialNormalizedReconstruction R n).comp
        (polynomialNormalizedReconstruction R n).adjoint-R.range.starProjection‖≤
      ((1-κ)^(2^n)/Real.sqrt κ)*(2+(1-κ)^(2^n)/Real.sqrt κ) := by
  rw [←normalizedEmbedding_cogram R hκ hR]
  apply cogram_error_of_isometry_approx
  · apply opNorm_le_bound _ zero_le_one
    intro x
    rw [normalizedReconstruction_norm R hκ hR,one_mul]
  · exact div_nonneg (pow_nonneg (sub_nonneg.mpr hκ1) _) (Real.sqrt_nonneg _)
  · exact polynomialNormalizedReconstruction_error R hκ hκ1 hR hRn n

/-- Every proved lower bounded embedding has a contractive rescaling
with the same range and explicit polynomial projection approximants. -/
theorem exists_scaled_projection_approximation (R : V →L[ℂ] H) [CompleteSpace R.range]
    {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    ∃ (S : V →L[ℂ] H) (κ : ℝ),0<κ ∧ κ≤1 ∧ ‖S‖≤1 ∧ S.range=R.range ∧
      ∀ n : ℕ,‖(polynomialNormalizedReconstruction S n).comp
        (polynomialNormalizedReconstruction S n).adjoint-R.range.starProjection‖≤
          ((1-κ)^(2^n)/Real.sqrt κ)*(2+(1-κ)^(2^n)/Real.sqrt κ) := by
  let B := ‖R‖+1
  have hB : 0<B := by dsimp only [B]; positivity
  let S : V →L[ℂ] H := (B⁻¹ : ℝ) • R
  let κ : ℝ := min (a*(B⁻¹)^2) 1
  have hk : 0<κ := lt_min (mul_pos ha (sq_pos_of_pos (inv_pos.mpr hB))) zero_lt_one
  have hk1 : κ≤1 := min_le_right _ _
  have hn : ‖S‖≤1 := scaled_norm_le_one R hB (by dsimp only [B]; linarith)
  have hl (x : V) : κ*‖x‖^2≤‖S x‖^2 := by
    calc
      _ ≤ (a*(B⁻¹)^2)*‖x‖^2 := mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ = (B⁻¹)^2*(a*‖x‖^2) := by ring
      _ ≤ (B⁻¹)^2*‖R x‖^2 := mul_le_mul_of_nonneg_left (hR x) (sq_nonneg _)
      _ = ‖S x‖^2 := by
        rw [show S x=(B⁻¹ : ℝ) • R x from rfl,norm_smul,Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hB),mul_pow]
  have hr : S.range=R.range := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact ⟨(B⁻¹ : ℝ) • x,R.map_smul_of_tower _ _⟩
    · rintro _ ⟨x,rfl⟩
      refine ⟨(B : ℝ) • x,?_⟩
      change (B⁻¹ : ℝ) • R (B • x)=R x
      rw [R.map_smul_of_tower,smul_smul,inv_mul_cancel₀ hB.ne',one_smul]
  let : CompleteSpace S.range := by rw [hr]; infer_instance
  refine ⟨S,κ,hk,hk1,hn,hr,?_⟩
  intro n
  have he := polynomial_embedding_projection_error S hk hk1 hl hn n
  simpa only [hr] using he

#print axioms exists_scaled_projection_approximation

#print axioms cogram_error_of_isometry_approx
#print axioms polynomial_embedding_projection_error

end QuantitativeMaass
