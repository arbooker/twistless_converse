module

public import AsymptoticRegularInclusionV1
public import AsymptoticReconstructedCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip terminalConstant)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The same parameters already used by the literal Euler count also
contract the regular counting realization, at every orbit root. -/
theorem parameters_contraction (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (hχ : ∀ q,q∣Q → ‖χ q‖=1) (z : ℍ) :
    ‖low A hN (AsymptoticReconstructedCount.parameters A P) χ
      ((AsymptoticReconstructedCount.parameters A P).s+3) z‖<1/2 :=
  (low_norm_le A hN _ χ hχ (by omega) z).trans_lt
    (AsymptoticReconstructedCount.parameters_bound A P)

/-- The actual regular extension followed by the change of capped exponent
from s+3 to s+4. This is the counting counterpart of the map used in the
holomorphic count-to-trace inequality. -/
noncomputable def includedExtension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    TerminalSpace A P z →L[ℂ] Space :=
  (AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp (extension A hN P χ z)

theorem includedExtension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    highProjection A P z (includedExtension A hN P χ z g)=(g:Space) := by
  change AsymptoticOrbitDiagonal.corner (highStrip P.ε) z
    (AsymptoticRegularInclusion.inclusion P.epsilon_pos z (extension A hN P χ z g))=_
  rw [AsymptoticRegularInclusion.corner_inclusion P.epsilon_pos (highStrip P.ε)
    (fun _ hz => hz.2)]
  exact extension_terminal A hN P χ z hK g

theorem includedExtension_norm_ge (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    ‖g‖≤‖includedExtension A hN P χ z g‖ := by
  calc
    ‖g‖=‖highProjection A P z (includedExtension A hN P χ z g)‖ := by
      rw [includedExtension_terminal A hN P χ z hK g]
      rfl
    _ ≤ ‖includedExtension A hN P χ z g‖ := by
      simpa only [one_mul] using (highProjection A P z).le_of_opNorm_le
        (highProjection_norm_le A P z) (includedExtension A hN P χ z g)

theorem includedExtension_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖includedExtension A hN P χ z‖≤1+2*terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply le_trans (mul_le_mul_of_nonneg_right
    (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z) (norm_nonneg _))
  simpa only [one_mul] using extension_norm_le A hN P χ hχ z hK

noncomputable def includedFull (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    Space →L[ℂ] Space :=
  (AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp (full A hN P χ z)

theorem includedFull_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : Space) :
    highProjection A P z (includedFull A hN P χ z f)=highProjection A P z f :=
  includedExtension_terminal A hN P χ z hK
    (AsymptoticOrbitRegion.restrict (highStrip P.ε) z f)

theorem includedFull_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖includedFull A hN P χ z‖≤1+2*terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply le_trans (mul_le_mul_of_nonneg_right
    (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos z) (norm_nonneg _))
  simpa only [one_mul] using full_norm_le A hN P χ hχ z hK

theorem includedFull_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) : Covariant (includedFull A hN P χ) :=
  covariant_comp _ _ (AsymptoticRegularInclusion.inclusion_covariant P.epsilon_pos)
    (full_covariant A hN P χ hK)

theorem includedFull_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (includedFull A hN P χ z) g h) :=
  matrix_comp_measurable _ _ (AsymptoticRegularInclusion.inclusion_matrix_measurable P.epsilon_pos)
    (full_matrix_measurable A hN P χ hK) g h

theorem includedFull_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    (includedFull A hN P χ z).comp (highProjection A P z)=includedFull A hN P χ z :=
  congrArg (fun X : Space →L[ℂ] Space => (AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp X)
    (full_right_terminal A hN P χ z)

theorem includedFull_gram_trace_finite (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1/2) :
    trace volume (fun z => (includedFull A hN P χ z).adjoint.comp (includedFull A hN P χ z))<∞ := by
  apply AsymptoticHyperbolicArea.closed_terminal_trace_finite
    (C:=(1+2*terminalConstant A P)^2) P.epsilon_pos
  · intro z
    have hn := includedFull_norm_le A hN P χ hχ z (hK z)
    apply (opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg (includedFull A hN P χ z))
      ((norm_nonneg (includedFull A hN P χ z)).trans hn)
  · intro z
    exact congrArg (fun X : Space →L[ℂ] Space => (includedFull A hN P χ z).adjoint.comp X)
      (includedFull_right_terminal A hN P χ z)

theorem includedFull_range_gram_trace_finite (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hK : ∀ z,‖low A hN P χ (P.s+3) z‖<1/2) :
    trace volume (fun z => (includedFull A hN P χ z).comp (includedFull A hN P χ z).adjoint)<∞ := by
  have hk : ∀ z,‖low A hN P χ (P.s+3) z‖<1 := fun z => lt_trans (hK z) (by norm_num)
  rw [← rational_trace_adjoint_mul (includedFull A hN P χ)
    (includedFull_matrix_measurable A hN P χ hk) (includedFull_covariant A hN P χ hk)]
  exact includedFull_gram_trace_finite A hN P χ hχ hK

#print axioms parameters_contraction
#print axioms includedExtension_terminal
#print axioms includedExtension_norm_ge
#print axioms includedExtension_norm_le
#print axioms includedFull_terminal
#print axioms includedFull_norm_le
#print axioms includedFull_covariant
#print axioms includedFull_matrix_measurable
#print axioms includedFull_right_terminal
#print axioms includedFull_gram_trace_finite
#print axioms includedFull_range_gram_trace_finite

end AsymptoticRegularReconstruction
