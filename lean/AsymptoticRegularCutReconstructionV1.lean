module

public import AsymptoticRegularHeightCutoffV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip terminalConstant)
open AsymptoticRegularHeightCutoff

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def cutFull (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  (projection Y z).comp (includedFull A hN P χ z)

noncomputable def cutExtension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (z : ℍ) :
    TerminalSpace A P z →L[ℂ] Space :=
  (projection Y z).comp (includedExtension A hN P χ z)

theorem highProjection_cut (P : Parameters A) (Y : ℝ) (hY : Y≤P.ε) (z : ℍ) :
    (highProjection A P z).comp (projection Y z)=highProjection A P z :=
  AsymptoticOrbitDiagonal.corner_comp_of_subset (fun _ hz => hY.trans hz.2) z

theorem cutFull_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (hY : Y≤P.ε) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : Space) :
    highProjection A P z (cutFull A hN P χ Y z f)=highProjection A P z f :=
  (congrArg (fun T : Space →L[ℂ] Space => T (includedFull A hN P χ z f))
    (highProjection_cut A P Y hY z)).trans (includedFull_terminal A hN P χ z hK f)

theorem cutExtension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (hY : Y≤P.ε) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : TerminalSpace A P z) :
    highProjection A P z (cutExtension A hN P χ Y z f)=(f:Space) :=
  (congrArg (fun T : Space →L[ℂ] Space => T (includedExtension A hN P χ z f))
    (highProjection_cut A P Y hY z)).trans (includedExtension_terminal A hN P χ z hK f)

theorem cutExtension_norm_ge (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (hY : Y≤P.ε) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : TerminalSpace A P z) :
    ‖f‖≤‖cutExtension A hN P χ Y z f‖ := by
  have he := congrArg norm (cutExtension_terminal A hN P χ Y hY z hK f)
  calc
    ‖f‖=‖highProjection A P z (cutExtension A hN P χ Y z f)‖ := he.symm
    _ ≤ _ := by simpa only [one_mul] using
      (highProjection A P z).le_of_opNorm_le (highProjection_norm_le A P z) (cutExtension A hN P χ Y z f)

theorem cutFull_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ) (z : ℍ) :
    (cutFull A hN P χ Y z).comp (highProjection A P z)=cutFull A hN P χ Y z :=
  congrArg (fun T : Space →L[ℂ] Space => (projection Y z).comp T) (includedFull_right_terminal A hN P χ z)

theorem cutFull_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (Y : ℝ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖cutFull A hN P χ Y z‖≤1+2*terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (projection_norm_le Y z) (norm_nonneg _)).trans
  simpa only [one_mul] using includedFull_norm_le A hN P χ hχ z hK

/-- The extra capped power gives a uniform low-height removal error.
The bound retains all folds and applies to the actual reconstruction. -/
theorem cutFull_error (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (Y : ℝ) (hY : 0≤Y) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖includedFull A hN P χ z-cutFull A hN P χ Y z‖≤Y/P.ε*(1+2*terminalConstant A P) := by
  have he : includedFull A hN P χ z-cutFull A hN P χ Y z=
      (AsymptoticRegularInclusion.inclusion P.epsilon_pos z-
        (projection Y z).comp (AsymptoticRegularInclusion.inclusion P.epsilon_pos z)).comp (full A hN P χ z) := rfl
  rw [he]
  exact (opNorm_comp_le _ _).trans (mul_le_mul (inclusion_cut_error P.epsilon_pos hY z)
    (full_norm_le A hN P χ hχ z hK) (norm_nonneg _) (div_nonneg hY P.epsilon_pos.le))

theorem cutFull_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) : Covariant (cutFull A hN P χ Y) :=
  covariant_comp _ _ (projection_covariant Y) (includedFull_covariant A hN P χ hK)

theorem cutFull_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (Y : ℝ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutFull A hN P χ Y z) a b) :=
  matrix_comp_measurable _ _ (projection_matrix_measurable Y) (includedFull_matrix_measurable A hN P χ hK) a b

#print axioms cutFull_terminal
#print axioms cutExtension_norm_ge
#print axioms cutFull_right_terminal
#print axioms cutFull_norm_le
#print axioms cutFull_error
#print axioms cutFull_covariant
#print axioms cutFull_matrix_measurable

end AsymptoticRegularReconstruction
