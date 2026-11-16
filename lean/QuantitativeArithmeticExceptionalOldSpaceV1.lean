module

public import QuantitativeArithmeticExceptionalMomentsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Module
open QuantitativeArithmeticExceptionalMoments

namespace QuantitativeArithmeticExceptionalOldSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Every vector in an exceptional eigenspace belongs to the spectral
subspace, independently of the choice of orthonormal eigenbasis. -/
theorem eigen_mem_exceptional {C : E →ₗ[ℂ] E} (hC : C.IsSymmetric)
    (a μ : ℝ) (hμ : a ≤ |μ|) (v : E) (hv : C v = (μ : ℂ) • v) :
    v ∈ exceptionalSpace hC a := by
  classical
  rw [← (hC.eigenvectorBasis rfl).sum_repr v]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : a ≤ |hC.eigenvalues rfl i|
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩, rfl⟩
  · have hne : (hC.eigenvalues rfl i : ℂ) ≠ (μ : ℂ) := by
      intro he
      have he' : hC.eigenvalues rfl i = μ := Complex.ofReal_injective he
      exact hi (he' ▸ hμ)
    have hh := congrArg (fun w => (hC.eigenvectorBasis rfl).repr w i) hv
    rw [hC.eigenvectorBasis_apply_self_apply rfl] at hh
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at hh
    have hz : (hC.eigenvectorBasis rfl).repr v i = 0 := by
      apply (mul_eq_zero.mp (show
        ((hC.eigenvalues rfl i : ℂ)-(μ : ℂ))*
          (hC.eigenvectorBasis rfl).repr v i=0 by
            rw [sub_mul]
            exact sub_eq_zero.mpr hh)).resolve_left
      exact sub_ne_zero.mpr hne
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

/-- The exact Gram relations for two isometric inclusions. The maps
`A'` and `B'` will be the two normalized physical trace maps. -/
structure PairedGram (A B : E →ₗ[ℂ] F) (A' B' : F →ₗ[ℂ] E)
    (C : E →ₗ[ℂ] E) : Prop where
  aa : ∀ x, A' (A x) = x
  bb : ∀ x, B' (B x) = x
  ab : ∀ x, A' (B x) = C x
  ba : ∀ x, B' (A x) = C x

omit [FiniteDimensional ℂ F] in
/-- A small positive eigenvector of the sum of the two old projections
lies in the images of the exceptional lower-level spectral space. No
norm estimate involving an inverse Gram matrix is used. -/
theorem small_eigen_mem_images (A B : E →ₗ[ℂ] F) (A' B' : F →ₗ[ℂ] E)
    {C : E →ₗ[ℂ] E} (hC : C.IsSymmetric) (hG : PairedGram A B A' B' C)
    (a μ : ℝ) (hμ : 0 < μ) (haμ : μ ≤ 1-a)
    (v : F) (hv : A (A' v)+B (B' v) = (μ : ℂ) • v) :
    v ∈ (exceptionalSpace hC a).map A ⊔ (exceptionalSpace hC a).map B := by
  have hx := congrArg A' hv
  have hy := congrArg B' hv
  simp only [map_add, map_smul, hG.aa, hG.ab] at hx
  simp only [map_add, map_smul, hG.ba, hG.bb] at hy
  have hp : C (A' v+B' v) = ((μ-1 : ℝ) : ℂ) • (A' v+B' v) := by
    rw [map_add]
    have h1 : C (B' v) = (μ : ℂ) • A' v-A' v := (eq_sub_iff_add_eq').mpr hx
    have h2 : C (A' v) = (μ : ℂ) • B' v-B' v := (eq_sub_iff_add_eq).mpr hy
    rw [h1, h2, Complex.ofReal_sub, Complex.ofReal_one]
    module
  have hm : C (A' v-B' v) = ((1-μ : ℝ) : ℂ) • (A' v-B' v) := by
    rw [map_sub]
    have h1 : C (B' v) = (μ : ℂ) • A' v-A' v := (eq_sub_iff_add_eq').mpr hx
    have h2 : C (A' v) = (μ : ℂ) • B' v-B' v := (eq_sub_iff_add_eq).mpr hy
    rw [h1, h2, Complex.ofReal_sub, Complex.ofReal_one]
    module
  have hu := eigen_mem_exceptional hC a (μ-1)
    (by have := neg_le_abs (μ-1); linarith) _ hp
  have hw := eigen_mem_exceptional hC a (1-μ)
    (by have := le_abs_self (1-μ); linarith) _ hm
  have hxU : A' v ∈ exceptionalSpace hC a := by
    have hh := (exceptionalSpace hC a).smul_mem (1/2 : ℂ)
      ((exceptionalSpace hC a).add_mem hu hw)
    convert hh using 1
    module
  have hyU : B' v ∈ exceptionalSpace hC a := by
    have hh := (exceptionalSpace hC a).smul_mem (1/2 : ℂ)
      ((exceptionalSpace hC a).sub_mem hu hw)
    convert hh using 1
    module
  have hs : (μ : ℂ) • v ∈
      (exceptionalSpace hC a).map A ⊔ (exceptionalSpace hC a).map B := by
    rw [← hv]
    exact Submodule.add_mem_sup
      (Submodule.mem_map.mpr ⟨A' v, hxU, rfl⟩)
      (Submodule.mem_map.mpr ⟨B' v, hyU, rfl⟩)
  have hn : (μ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hμ
  have hh := ((exceptionalSpace hC a).map A ⊔ (exceptionalSpace hC a).map B).smul_mem
    ((μ : ℂ)⁻¹) hs
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh

def smallPositiveSpace {S : F →ₗ[ℂ] F} (hS : S.IsSymmetric) (η : ℝ) : Submodule ℂ F :=
  Submodule.span ℂ (Set.range (fun i : {i : Fin (finrank ℂ F) //
      0 < hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i ≤ η} =>
    hS.eigenvectorBasis rfl i.val))

/-- Exceptional rank transfers across two old inclusions with a factor
of two, even when their ranges meet at arbitrarily small angles. -/
theorem smallPositiveSpace_finrank (A B : E →ₗ[ℂ] F) (A' B' : F →ₗ[ℂ] E)
    {C : E →ₗ[ℂ] E} (hC : C.IsSymmetric) (hG : PairedGram A B A' B' C)
    (hS : (A.comp A'+B.comp B').IsSymmetric) (a : ℝ) :
    finrank ℂ (smallPositiveSpace hS (1-a)) ≤ 2*finrank ℂ (exceptionalSpace hC a) := by
  have hle : smallPositiveSpace hS (1-a) ≤
      (exceptionalSpace hC a).map A ⊔ (exceptionalSpace hC a).map B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact small_eigen_mem_images A B A' B' hC hG a (hS.eigenvalues rfl i.val)
      i.property.1 i.property.2 _ (hS.apply_eigenvectorBasis rfl i.val)
  exact (Submodule.finrank_mono hle).trans (two_image_finrank _ A B)

/-- The small positive spectrum is controlled by a lower-level even
moment, before any arithmetic or geometric estimate for that moment. -/
theorem smallPositiveSpace_moment (A B : E →ₗ[ℂ] F) (A' B' : F →ₗ[ℂ] E)
    {C : E →ₗ[ℂ] E} (hC : C.IsSymmetric) (hG : PairedGram A B A' B' C)
    (hS : (A.comp A'+B.comp B').IsSymmetric) (a : ℝ) (ha : 0 ≤ a) (d : ℕ) :
    a^(2*d)*(finrank ℂ (smallPositiveSpace hS (1-a)) : ℝ) ≤
      2*(LinearMap.trace ℂ E (C^(2*d))).re := by
  have hr := smallPositiveSpace_finrank A B A' B' hC hG hS a
  have hr' : (finrank ℂ (smallPositiveSpace hS (1-a)) : ℝ) ≤
      2*(finrank ℂ (exceptionalSpace hC a) : ℝ) := by exact_mod_cast hr
  have hb := exceptionalSpace_moment hC a ha d
  nlinarith [mul_le_mul_of_nonneg_left hr' (pow_nonneg ha (2*d))]

#print axioms eigen_mem_exceptional
#print axioms small_eigen_mem_images
#print axioms smallPositiveSpace_finrank
#print axioms smallPositiveSpace_moment

end QuantitativeArithmeticExceptionalOldSpace
