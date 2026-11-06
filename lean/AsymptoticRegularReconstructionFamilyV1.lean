module

public import AsymptoticRegularReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip highStrip_measurable terminalConstant)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Extend terminal restriction back into the whole counting space.
This gives a family on one fixed Hilbert space, suitable for rooted traces. -/
noncomputable def full (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) : Space →L[ℂ] Space :=
  (1+AsymptoticReconstruction.low (low A hN P χ (P.s+3) z)
    (terminal A hN P χ (by omega : 2≤P.s+3) z)).comp (highProjection A P z)

theorem full_eq_extension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) (f : Space) :
    full A hN P χ z f=extension A hN P χ z (AsymptoticOrbitRegion.restrict (highStrip P.ε) z f) := rfl

theorem full_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : Space) :
    highProjection A P z (full A hN P χ z f)=highProjection A P z f := by
  rw [full_eq_extension,extension_terminal A hN P χ z hK]
  rfl

theorem full_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖full A hN P χ z‖≤1+2*terminalConstant A P := by
  have he := extension_norm_le A hN P χ hχ z hK
  have hc : 0≤1+2*terminalConstant A P := (norm_nonneg (extension A hN P χ z)).trans he
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  rw [full_eq_extension]
  apply ((extension A hN P χ z).le_of_opNorm_le he _).trans
  apply mul_le_mul_of_nonneg_left _ hc
  change ‖highProjection A P z f‖≤‖f‖
  simpa only [one_mul] using (highProjection A P z).le_of_opNorm_le (highProjection_norm_le A P z) f

theorem full_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) : Covariant (full A hN P χ) := by
  apply covariant_comp
  · apply covariant_add
    · exact covariant_one
    · apply covariant_comp
      · apply covariant_tsum
        · intro z
          exact summable_geometric_of_norm_lt_one (hK z)
        · intro n
          exact covariant_pow _ (low_covariant A hN P χ (by omega)) n
      · exact terminal_covariant A hN P χ (by omega)
  · exact AsymptoticOrbitDiagonal.corner_covariant _

theorem full_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (full A hN P χ z) g h) := by
  apply matrix_comp_measurable
  · intro g h
    apply matrix_add_measurable
    · intro g h
      exact measurable_const
    · intro g h
      apply matrix_comp_measurable
      · intro g h
        apply matrix_tsum_measurable
        · intro z
          exact summable_geometric_of_norm_lt_one (hK z)
        · intro n g h
          exact matrix_pow_measurable _ (low_matrix_measurable A hN P χ (by omega)) n g h
      · exact terminal_matrix_measurable A hN P χ (by omega)
  · exact AsymptoticOrbitDiagonal.corner_matrix_measurable
      (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) (highStrip_measurable P.ε)

#print axioms full_eq_extension
#print axioms full_terminal
#print axioms full_norm_le
#print axioms full_covariant
#print axioms full_matrix_measurable

end AsymptoticRegularReconstruction
