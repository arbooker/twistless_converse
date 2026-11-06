module

public import AsymptoticRegularFiniteReconstructionV1
public import AsymptoticRegularPolynomialTraceV1
public import AsymptoticPolynomialObservationV1
public import AsymptoticSharedFiniteReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteCutNormal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (d : ℕ) (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.completedNormal (highProjection A P' z)
    (finiteCutFull A hN P' (multiplier e) Y d I z)
    (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)

theorem finiteCutNormal_formula (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := finiteCutFull A hN P' (multiplier e) Y d I z
    finiteCutNormal A hN P r s hs e Y d I z=
      R.adjoint.comp ((1+gram hN r s hs P'.epsilon_pos (P'.s+4) e z).comp R)+
        (1+(-1:ℂ) • highProjection A P' z) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := finiteCutFull A hN P' (multiplier e) Y d I z
  let L := observations hN r s hs P'.epsilon_pos (P'.s+4) e z
  change AsymptoticObservation.normal R L+1-highProjection A P' z=
    R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+(-1:ℂ) • highProjection A P' z)
  have he := congrArg (fun T : Space →L[ℂ] Space => T+1-highProjection A P' z)
    (AsymptoticObservation.normal_formula R L)
  have hneg : (-1:ℂ) • highProjection A P' z= -highProjection A P' z :=
    neg_one_smul ℂ (highProjection A P' z)
  apply he.trans
  calc
    _ = R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+ -highProjection A P' z) := by abel
    _ = _ := congrArg (fun T : Space →L[ℂ] Space =>
      R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+T)) hneg.symm

theorem finiteCutNormal_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    Covariant (finiteCutNormal A hN P r s hs e Y d I) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hc := finiteCutFull_covariant A hN P' (multiplier e) Y d I
  have he := funext (finiteCutNormal_formula A hN P r s hs e Y d I)
  rw [he]
  apply covariant_add
  · apply covariant_comp
    · exact covariant_adjoint _ hc
    · apply covariant_comp
      · exact covariant_add _ _ covariant_one (gram_covariant hN r s hs P'.epsilon_pos (P'.s+4) e)
      · exact hc
  · exact covariant_add _ _ covariant_one
      (covariant_smul _ _ (AsymptoticOrbitDiagonal.corner_covariant _))

theorem finiteCutNormal_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteCutNormal A hN P r s hs e Y d I z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hm := finiteCutFull_matrix_measurable A hN P' (multiplier e) Y d I
  simp only [finiteCutNormal_formula]
  apply matrix_add_measurable
  · intro c d
    apply matrix_comp_measurable
    · intro u v
      simp only [matrix_adjoint]
      exact Complex.continuous_conj.measurable.comp (hm v u)
    · intro u v
      apply matrix_comp_measurable
      · intro j k
        exact matrix_add_measurable _ _ (fun _ _ => measurable_const)
          (gram_matrix_measurable hN r s hs P'.epsilon_pos (P'.s+4) e) j k
      · exact hm
  · intro c d
    apply matrix_add_measurable
    · intro u v
      exact measurable_const
    · intro u v
      exact matrix_smul_measurable _ _
        (AsymptoticOrbitDiagonal.corner_matrix_measurable
          (fun g => (AsymptoticRationalBranches.action_continuous g).measurable)
          (AsymptoticCertificateOperators.highStrip_measurable P'.ε)) u v

theorem finiteCutNormal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (d : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutNormal A hN P r s hs e Y d I z‖≤wholeNormalBound A hN P r s hs := by
  apply AsymptoticObservation.completedNormal_norm_le
  · exact highProjection_norm_le A _ z
  · exact finiteCutFull_norm_le A hN _ (AsymptoticReconstructedCount.parameters_bound A P).le
      (multiplier e) (fun q _ => multiplier_norm e q) Y d I z
  · exact observations_norm_le hN r s hs _ _ e z

/-- Substitute the finite reconstruction into the same inverse polynomial
already used by the actual cutoff trace. Depth, folds and degree are finite. -/
noncomputable def finiteCutPolynomialTerminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  let R := finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  (polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (finiteCutNormal A hN P r s hs e Y d I z) n).comp (R.adjoint.comp R)

noncomputable def finitePolynomialErrorFactor (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.polynomialReconstructionLipschitz
    (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (1+2*AsymptoticCertificateOperators.terminalConstant A P')
    (observationsBound hN r s hs P'.epsilon_pos (P'.s+4)) n

theorem finitePolynomialErrorFactor_nonneg (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) :
    0≤finitePolynomialErrorFactor A hN P r s hs n := by
  apply AsymptoticObservation.polynomialReconstructionLipschitz_nonneg
  have ht : 0≤AsymptoticCertificateOperators.terminalConstant A
      (AsymptoticReconstructedCount.parameters A P) := by
    unfold AsymptoticCertificateOperators.terminalConstant
    positivity
  positivity

theorem finiteCutPolynomialTerminal_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutPolynomialTerminal A hN P r s hs e Y n d I z-
      cutPolynomialTerminal A hN P r s hs e Y n z‖≤
      finitePolynomialErrorFactor A hN P r s hs n*
        ‖finiteFoldFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) d I z-
          full A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z‖ := by
  apply (AsymptoticObservation.polynomial_gram_difference_norm_le _ _ _ _ _ _ _
    (highProjection_norm_le A _ z)
    (finiteCutFull_norm_le A hN _ (AsymptoticReconstructedCount.parameters_bound A P).le
      (multiplier e) (fun q _ => multiplier_norm e q) Y d I z)
    (cutFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z))
    (observations_norm_le hN r s hs _ _ e z) n).trans
  exact mul_le_mul_of_nonneg_left (finiteCutFull_error A hN _ (multiplier e) Y d I z)
    (finitePolynomialErrorFactor_nonneg A hN P r s hs n)

/-- A fixed finite polynomial of the actual observation normal admits
finite reconstruction expressions uniformly over every root and sector.
The same choices also work for every low-height cutoff. -/
theorem finiteCutPolynomialTerminal_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ d : ℕ,∃ I : Finset ℤ,∀ e : Sector N,∀ Y : ℝ,∀ z : ℍ,
      ‖finiteCutPolynomialTerminal A hN P r s hs e Y n d I z-
        cutPolynomialTerminal A hN P r s hs e Y n z‖<δ := by
  let C := finitePolynomialErrorFactor A hN P r s hs n
  have hC : 0≤C := finitePolynomialErrorFactor_nonneg A hN P r s hs n
  have hC1 : 0<1+C := by linarith
  have hδ' : 0<δ/(1+C) := div_pos hδ hC1
  obtain ⟨d,I,_,hI⟩ := AsymptoticSharedApproximation.finite_reconstruction_approximation A hN
    (AsymptoticReconstructedCount.parameters A P) (AsymptoticReconstructedCount.parameters_bound A P).le hδ'
  refine ⟨d,I,?_⟩
  intro e Y z
  have hh := hI ⟨multiplier e,fun q _ => multiplier_norm e q⟩ z
  apply (finiteCutPolynomialTerminal_error A hN P r s hs e Y n d I z).trans_lt
  have hb := mul_le_mul_of_nonneg_left hh.le hC
  have he : (1+C)*(δ/(1+C))=δ := mul_div_cancel₀ δ hC1.ne'
  nlinarith

#print axioms finiteCutNormal_formula
#print axioms finiteCutNormal_covariant
#print axioms finiteCutNormal_matrix_measurable
#print axioms finiteCutNormal_norm_le
#print axioms finitePolynomialErrorFactor_nonneg
#print axioms finiteCutPolynomialTerminal_error
#print axioms finiteCutPolynomialTerminal_approximation

end AsymptoticRegularObservation
