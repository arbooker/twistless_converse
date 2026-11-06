module

public import AsymptoticRegularFiniteAmbientTraceV1
public import AsymptoticRegularUpperCutoffV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCutPolynomialAmbient_diagonal_integrable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) :
    Integrable (fun z => (matrix (finiteCutPolynomialAmbient A hN P r s hs e Y n d I z) 1 1).re) volume := by
  let P' := AsymptoticReconstructedCount.parameters A P
  exact bounded_sandwich_diagonal_integrable volume AsymptoticRationalGroup.measurePreserving _ _
    (finiteCutFull_matrix_measurable A hN P' (multiplier e) Y d I)
    (polynomial_matrix_measurable _ _ (finiteCutNormal_matrix_measurable A hN P r s hs e Y d I) n)
    (finiteCutFull_covariant A hN P' (multiplier e) Y d I)
    (finiteCutFull_gram_trace_finite A hN P e Y d I)
    (fun z => polynomial_norm_le_of_bound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
      _ (finiteCutNormal_norm_le A hN P r s hs e Y d I z) n)

theorem finiteCutPolynomialAmbient_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutPolynomialAmbient A hN P r s hs e Y n d I z‖≤
      polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
        (wholeNormalBound A hN P r s hs) n*
          (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  let R := finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  have hR := finiteCutFull_norm_le A hN _ (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) Y d I z
  have hi := polynomial_norm_le_of_bound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    _ (finiteCutNormal_norm_le A hN P r s hs e Y d I z) n
  apply (opNorm_comp_le _ _).trans
  have hinner := (opNorm_comp_le _ _).trans
    (mul_le_mul hi (by simpa only [adjoint.norm_map] using hR)
      (norm_nonneg R.adjoint) ((norm_nonneg _).trans hi))
  apply (mul_le_mul hR hinner (norm_nonneg _) ((norm_nonneg R).trans hR)).trans_eq
  ring

noncomputable def finiteUpperCutPolynomialTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y H : ℝ)
    (n d : ℕ) (I : Finset ℤ) : ℝ :=
  signedTrace volume (AsymptoticRegularUpperCutoff.cut H
    (finiteCutPolynomialAmbient A hN P r s hs e Y n d I))

theorem finiteUpperCutPolynomialTrace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) {H : ℝ} (hH : 0<H)
    (n d : ℕ) (I : Finset ℤ) :
    ‖signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
      finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I‖≤
      (polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
        (wholeNormalBound A hN P r s hs) n*
          (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2)/H := by
  rw [← finiteCutPolynomialAmbient_trace_eq_terminal A hN P r s hs e Y n d I]
  exact AsymptoticRegularUpperCutoff.trace_error hH _
    (finiteCutPolynomialAmbient_norm_le A hN P r s hs e Y n d I)
    (finiteCutPolynomialAmbient_diagonal_integrable A hN P r s hs e Y n d I)

/-- The same fixed upper strip works for all sectors, lower cutoffs,
finite fold sets and depths. -/
theorem finiteUpperCutPolynomialTrace_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ H₀ : ℝ, 0<H₀ ∧ ∀ H : ℝ, H₀≤H →
      ∀ e : Sector N, ∀ Y : ℝ, ∀ d : ℕ, ∀ I : Finset ℤ,
        ‖signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
          finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I‖<δ := by
  let C := polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (wholeNormalBound A hN P r s hs) n*
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2
  have hH₀ : 0 < |C|/δ+1 := by positivity
  refine ⟨|C|/δ+1,hH₀,?_⟩
  intro H hH e Y d I
  have hHp : 0<H := hH₀.trans_le hH
  apply (finiteUpperCutPolynomialTrace_error A hN P r s hs e Y hHp n d I).trans_lt
  change C/H<δ
  apply (div_lt_iff₀ hHp).mpr
  have hc : |C|/δ*δ=|C| := div_mul_cancel₀ _ hδ.ne'
  have hh := mul_le_mul_of_nonneg_right hH hδ.le
  nlinarith [le_abs_self C]

#print axioms finiteCutPolynomialAmbient_diagonal_integrable
#print axioms finiteCutPolynomialAmbient_norm_le
#print axioms finiteUpperCutPolynomialTrace_error
#print axioms finiteUpperCutPolynomialTrace_approximation

end AsymptoticRegularObservation
