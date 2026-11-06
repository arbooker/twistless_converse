module

public import AsymptoticFiniteFoldReconstructionV1
public import AsymptoticRegularCutReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip highStrip_measurable terminalConstant lowConstant)
open AsymptoticRegularHeightCutoff

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteFoldFull_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) : Covariant (finiteFoldFull A hN P χ n I) := by
  apply covariant_comp
  · apply covariant_add
    · exact covariant_one
    · apply covariant_comp
      · apply covariant_finsetSum
        intro j _
        exact covariant_pow _ (finiteLow_covariant A hN P χ (P.s+3) I) j
      · exact finiteTerminal_covariant A hN P χ (by omega) I
  · exact AsymptoticOrbitDiagonal.corner_covariant _

theorem finiteFoldFull_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteFoldFull A hN P χ n I z) g h) := by
  apply matrix_comp_measurable
  · intro g h
    apply matrix_add_measurable
    · intro g h
      exact measurable_const
    · intro g h
      apply matrix_comp_measurable
      · intro g h
        apply matrix_finsetSum_measurable
        intro j _ g h
        exact matrix_pow_measurable _ (finiteLow_matrix_measurable A hN P χ (P.s+3) I) j g h
      · exact finiteTerminal_matrix_measurable A hN P χ (by omega) I
  · exact AsymptoticOrbitDiagonal.corner_matrix_measurable
      (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) (highStrip_measurable P.ε)

theorem finiteFoldFull_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    (finiteFoldFull A hN P χ n I z).comp (highProjection A P z)=finiteFoldFull A hN P χ n I z := by
  unfold finiteFoldFull
  rw [comp_assoc]
  exact congrArg (fun T : Space →L[ℂ] Space => (1+AsymptoticReconstruction.finiteLow
    (finiteLow A hN P χ (P.s+3) I z) (finiteTerminal A hN P χ (by omega) I z) n).comp T)
    (AsymptoticOrbitDiagonal.corner_idempotent _ z)

/-- The finite reconstruction with the actual extra capped weight and
low-height cutoff used in the observation operator. -/
noncomputable def finiteCutFull (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  (projection Y z).comp ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp
    (finiteFoldFull A hN P χ n I z))

theorem finiteCutFull_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    (finiteCutFull A hN P χ Y n I z).comp (highProjection A P z)=finiteCutFull A hN P χ Y n I z :=
  congrArg (fun T : Space →L[ℂ] Space => (projection Y z).comp
    ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp T))
    (finiteFoldFull_right_terminal A hN P χ n I z)

theorem finiteCutFull_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) : Covariant (finiteCutFull A hN P χ Y n I) :=
  covariant_comp _ _ (projection_covariant Y)
    (covariant_comp _ _ (AsymptoticRegularInclusion.inclusion_covariant P.epsilon_pos)
      (finiteFoldFull_covariant A hN P χ n I))

theorem finiteCutFull_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteCutFull A hN P χ Y n I z) a b) :=
  matrix_comp_measurable _ _ (projection_matrix_measurable Y)
    (matrix_comp_measurable _ _ (AsymptoticRegularInclusion.inclusion_matrix_measurable P.epsilon_pos)
      (finiteFoldFull_matrix_measurable A hN P χ n I)) a b

theorem finiteCutFull_norm_le (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1/2) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (Y : ℝ) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutFull A hN P χ Y n I z‖≤1+2*terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (projection_norm_le Y z) (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right
    (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z) (norm_nonneg _)).trans
  simpa only [one_mul] using finiteFoldFull_norm_le A hN P hP χ hχ n I z

theorem finiteCutFull_error (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutFull A hN P χ Y n I z-cutFull A hN P χ Y z‖≤
      ‖finiteFoldFull A hN P χ n I z-full A hN P χ z‖ := by
  have he : finiteCutFull A hN P χ Y n I z-cutFull A hN P χ Y z=
      (projection Y z).comp ((AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp
        (finiteFoldFull A hN P χ n I z-full A hN P χ z)) := by
    simp only [finiteCutFull,cutFull,includedFull,comp_sub]
  rw [he]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (projection_norm_le Y z) (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z) (norm_nonneg _)

#print axioms finiteFoldFull_covariant
#print axioms finiteFoldFull_matrix_measurable
#print axioms finiteFoldFull_right_terminal
#print axioms finiteCutFull_right_terminal
#print axioms finiteCutFull_covariant
#print axioms finiteCutFull_matrix_measurable
#print axioms finiteCutFull_norm_le
#print axioms finiteCutFull_error

end AsymptoticRegularReconstruction
