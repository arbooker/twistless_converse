module

public import AsymptoticCylinderInversePolynomialV1
public import AsymptoticPolynomialObservationV1
public import AsymptoticGramTracePerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap AsymptoticCoerciveNeumann AsymptoticDiagonalTrace AsymptoticFourierNorm

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem sandwich_sub_norm_le_of_bounds (R S : G →L[ℂ] H) (I J : G →L[ℂ] G)
    (BR BI : ℝ) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR) (hI : ‖I‖≤BI) (hJ : ‖J‖≤BI) :
    ‖R.comp (I.comp R.adjoint)-S.comp (J.comp S.adjoint)‖≤
      2*BR*BI*‖R-S‖+BR^2*‖I-J‖ := by
  have hBR : 0≤BR := (norm_nonneg R).trans hR
  have hBI : 0≤BI := (norm_nonneg I).trans hI
  apply (sandwich_sub_norm_le_general R S I J).trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h₁ := mul_le_mul hR hI (norm_nonneg I) hBR
    have h₂ := mul_le_mul hS hJ (norm_nonneg J) hBR
    nlinarith
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_two] using mul_le_mul hS hR (norm_nonneg R) hBR

/-- Factoring out the extra capped-weight inclusion leaves a uniformly
small bounded middle operator, even when reconstruction itself varies. -/
theorem factored_polynomial_sandwich_error (C : ℝ) (A : H →L[ℂ] H) (R S : G →L[ℂ] H)
    (L : H →L[ℂ] J) (BR BL : ℝ) (hA : ‖A‖≤1) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR)
    (hL : ‖L‖≤BL) (n : ℕ) :
    ‖R.comp ((polynomial C (normal (A.comp R) L) n).comp R.adjoint)-
      S.comp ((polynomial C (normal (A.comp S) L) n).comp S.adjoint)‖≤
      polynomialReconstructionLipschitz C BR BL n*‖R-S‖ := by
  let D := BR^2+(BL*BR)^2+2
  have hBR : 0≤BR := (norm_nonneg R).trans hR
  have hAR : ‖A.comp R‖≤BR := (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hA (norm_nonneg R)).trans (by simpa only [one_mul] using hR))
  have hAS : ‖A.comp S‖≤BR := (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hA (norm_nonneg S)).trans (by simpa only [one_mul] using hS))
  have hMR : ‖normal (A.comp R) L‖≤D :=
    (normal_norm_le_of_bounds _ L BR BL hAR hL).trans (by dsimp [D]; linarith)
  have hMS : ‖normal (A.comp S) L‖≤D :=
    (normal_norm_le_of_bounds _ L BR BL hAS hL).trans (by dsimp [D]; linarith)
  have hAD : ‖A.comp R-A.comp S‖≤‖R-S‖ := by
    rw [← comp_sub]
    apply (opNorm_comp_le _ _).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (norm_nonneg (R-S))
  have hMD : ‖normal (A.comp R) L-normal (A.comp S) L‖≤2*BR*(1+BL^2)*‖R-S‖ := by
    apply (normal_sub_norm_le (A.comp R) (A.comp S) L).trans
    have hsum : ‖A.comp R‖+‖A.comp S‖≤2*BR := by linarith
    exact mul_le_mul
      (mul_le_mul hsum (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg L) hL 2))
        (by positivity) (by positivity)) hAD (norm_nonneg _) (by positivity)
  have hLip : 0≤polynomialLipschitz C D n := by
    have hc := (scale_pos C).le
    dsimp [polynomialLipschitz,D]
    positivity
  have hi := (polynomial_difference_norm_le C _ _ hMR hMS n).trans
    (mul_le_mul_of_nonneg_left hMD hLip)
  apply (sandwich_sub_norm_le_of_bounds R S _ _ BR (polynomialBound C D n) hR hS
    (polynomial_norm_le_of_bound C _ hMR n) (polynomial_norm_le_of_bound C _ hMS n)).trans
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hi (sq_nonneg BR))).trans_eq
  unfold polynomialReconstructionLipschitz
  dsimp [D]
  ring

omit [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] in
theorem compressedSandwich_comp (A : H →L[ℂ] H) (R : G →L[ℂ] H) (I : G →L[ℂ] G)
    (U : Submodule ℂ H) [CompleteSpace U] :
    compressedSandwich (A.comp R) I U=compressedSandwich A (R.comp (I.comp R.adjoint)) U := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [compressedSandwich,comp_apply,adjoint_comp]

/-- The capped inclusion turns finite-reconstruction error into O(delta*k)
Fourier trace error, without requiring positive approximating polynomials. -/
theorem factored_polynomial_trace_error (C : ℝ) (A : H →L[ℂ] H) (R S : G →L[ℂ] H)
    (L : H →L[ℂ] J) (BR BL : ℝ) (hA : ‖A‖≤1) (hR : ‖R‖≤BR) (hS : ‖S‖≤BR)
    (hL : ‖L‖≤BL) (n : ℕ) (U : Submodule ℂ H) [CompleteSpace U]
    (b : HilbertBasis ℕ ℂ U) (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε)
    (hg : ∀ j,‖A.adjoint ((b j:U):H)‖^2≤modeRatio m t scale ε (j+1)) :
    ‖trace b (compressedSandwich (A.comp R) (polynomial C (normal (A.comp R) L) n) U)-
      trace b (compressedSandwich (A.comp S) (polynomial C (normal (A.comp S) L) n) U)‖≤
      polynomialReconstructionLipschitz C BR BL n*‖R-S‖*
        (1+majorantConstant t scale ε)*(m+2:ℕ) := by
  rw [compressedSandwich_comp,compressedSandwich_comp]
  simpa only [mul_one] using compressedSandwich_trace_error A _ _ U b m t hs hε zero_le_one
    (fun j => by simpa only [one_mul] using hg j)
    (factored_polynomial_sandwich_error C A R S L BR BL hA hR hS hL n)

#print axioms sandwich_sub_norm_le_of_bounds
#print axioms factored_polynomial_sandwich_error
#print axioms compressedSandwich_comp
#print axioms factored_polynomial_trace_error

end AsymptoticObservation
