module

public import AsymptoticRegularBoundedSandwichV1
public import AsymptoticRegularFinitePolynomialTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open scoped ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCutFull_gram_trace_finite (hN : 0<N) (P : Parameters A) (e : Sector N)
    (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    trace volume (fun z => (finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P)
      (multiplier e) Y d I z).adjoint.comp
        (finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z))<∞ := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := finiteCutFull A hN P' (multiplier e) Y d I
  apply AsymptoticHyperbolicArea.closed_terminal_trace_finite
    (C := (1+2*AsymptoticCertificateOperators.terminalConstant A P')^2) P'.epsilon_pos
  · intro z
    have hn := finiteCutFull_norm_le A hN P' (AsymptoticReconstructedCount.parameters_bound A P).le
      (multiplier e) (fun q _ => multiplier_norm e q) Y d I z
    rw [norm_adjoint_comp_self]
    simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg (R z)) hn 2
  · intro z
    exact congrArg (fun X : Space →L[ℂ] Space => (R z).adjoint.comp X)
      (finiteCutFull_right_terminal A hN P' (multiplier e) Y d I z)

#print axioms finiteCutFull_gram_trace_finite

end AsymptoticRegularReconstruction

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteCutPolynomialAmbient (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  let R := finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  R.comp ((polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (finiteCutNormal A hN P r s hs e Y d I z) n).comp R.adjoint)

/-- The ambient polynomial trace equals the terminal expression already
used in the finite-word reduction, with all finiteness and covariance
conditions discharged for the actual reconstruction. -/
theorem finiteCutPolynomialAmbient_trace_eq_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) :
    signedTrace volume (finiteCutPolynomialAmbient A hN P r s hs e Y n d I)=
      signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let J := fun z => polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (finiteCutNormal A hN P r s hs e Y d I z) n
  have hj := fun z => polynomial_norm_le_of_bound
    (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    _ (finiteCutNormal_norm_le A hN P r s hs e Y d I z) n
  exact signedTrace_bounded_sandwich volume AsymptoticRationalGroup.measurePreserving _ J
    (finiteCutFull_matrix_measurable A hN P' (multiplier e) Y d I)
    (polynomial_matrix_measurable _ _ (finiteCutNormal_matrix_measurable A hN P r s hs e Y d I) n)
    (finiteCutFull_covariant A hN P' (multiplier e) Y d I)
    (polynomial_covariant _ _ (finiteCutNormal_covariant A hN P r s hs e Y d I) n)
    (finiteCutFull_gram_trace_finite A hN P e Y d I)
    hj

#print axioms finiteCutPolynomialAmbient_trace_eq_terminal

end AsymptoticRegularObservation
