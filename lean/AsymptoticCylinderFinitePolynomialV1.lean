module

public import AsymptoticFactoredPolynomialTraceV1
public import AsymptoticCylinderFiniteReconstructionV1
public import AsymptoticCylinderPolynomialTraceV1
public import AsymptoticSharedFiniteReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticReconstructedCount AsymptoticCoerciveNeumann
open AsymptoticDiagonalTrace AsymptoticFourierNorm
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteCutNormal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (d : ℕ) (I : Finset ℤ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] AsymptoticCylinderTerminal.Space (parameters A P).ε :=
  normal (finiteCutReconstruction A hN P h e Y d I)
    (AsymptoticCompactObservationCount.observations hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e)

theorem finiteCutNormal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (d : ℕ) (I : Finset ℤ) : ‖finiteCutNormal A hN P r s hs h e Y d I‖≤normalBound A hN P r s hs :=
  normal_norm_le_of_bounds _ _ _ _ (finiteCutReconstruction_norm_le A hN P h e Y d I)
    (AsymptoticCompactObservationCount.observations_norm_le hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e)

noncomputable def finiteCutInversePolynomial (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] AsymptoticCylinderTerminal.Space (parameters A P).ε :=
  polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (finiteCutNormal A hN P r s hs h e Y d I) n

noncomputable def finiteCutPolynomialTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) : ℝ :=
  trace (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (compressedSandwich (finiteCutReconstruction A hN P h e Y d I)
      (finiteCutInversePolynomial A hN P r s hs h e Y n d I)
      (holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos))

noncomputable def finitePolynomialErrorFactor (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) : ℝ :=
  polynomialReconstructionLipschitz (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)) (observationsBound A hN P r s hs) n*
      (1+majorantConstant ((parameters A P).s+4) (4*Real.pi) (parameters A P).ε)

theorem finitePolynomialErrorFactor_nonneg (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) :
    0≤finitePolynomialErrorFactor A hN P r s hs n := by
  apply mul_nonneg
  · apply polynomialReconstructionLipschitz_nonneg
    have ht : 0≤AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
      unfold AsymptoticCertificateOperators.terminalConstant
      positivity
    positivity
  · unfold majorantConstant
    positivity

set_option maxHeartbeats 800000 in
/-- The error is controlled before the extra capped weight is applied;
the Fourier trace estimate is therefore uniform in every weight. -/
theorem finiteCutPolynomialTrace_normalized_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) :
    ‖finiteCutPolynomialTrace A hN P r s hs h e Y n d I-cutPolynomialTrace A hN P r s hs h e Y n‖/(2*h+2:ℕ)≤
      finitePolynomialErrorFactor A hN P r s hs n*
        ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN (parameters A P) (multiplier e) d I (h+1)-
          AsymptoticGeometricReconstruction.extension A hN (parameters A P) (multiplier e) (h+1)‖ := by
  let P' := parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  let L := AsymptoticCompactObservationCount.observations hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  have ht := factored_polynomial_trace_error (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    (inclusion P'.epsilon_pos) (finiteCutBaseReconstruction A hN P h e Y d I) (cutBaseReconstruction A hN P h e Y)
    L BR (observationsBound A hN P r s hs) (inclusion_norm_le P'.epsilon_pos)
    (finiteCutBaseReconstruction_norm_le A hN P h e Y d I) (cutBaseReconstruction_norm_le A hN P h e Y)
    (AsymptoticCompactObservationCount.observations_norm_le hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e) n
    (holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)
    (fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)
    (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos (fun j => by
      simp only [fourierBasis_apply,modeInSpace]
      rw [inclusion_adjoint_unitMode_norm_sq,modeRatio,ite_eq_right (by omega : j+1≠0)])
  have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
  have hd := div_le_div_of_nonneg_right ht hk.le
  rw [mul_div_cancel_right₀ _ hk.ne'] at hd
  have he : ‖finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
      cutPolynomialTrace A hN P r s hs h e Y n‖/(2*h+2:ℕ)≤
      finitePolynomialErrorFactor A hN P r s hs n*
        ‖finiteCutBaseReconstruction A hN P h e Y d I-cutBaseReconstruction A hN P h e Y‖ := by
    convert hd using 1
    · simp only [finiteCutPolynomialTrace,cutPolynomialTrace,finiteCutInversePolynomial,cutInversePolynomial,
        finiteCutNormal,cutNormal,finiteCutReconstruction,cutReconstruction_eq_weighted,cutBaseReconstruction,L,P']
    · unfold finitePolynomialErrorFactor
      dsimp [BR,P']
      ring
  exact he.trans (mul_le_mul_of_nonneg_left (finiteCutBaseReconstruction_error A hN P h e Y d I)
    (finitePolynomialErrorFactor_nonneg A hN P r s hs n))

theorem finiteCutPolynomialTrace_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ d : ℕ,∃ I : Finset ℤ,∀ h : ℕ,∀ e : Sector N,∀ Y : ℝ,
      ‖finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
        cutPolynomialTrace A hN P r s hs h e Y n‖/(2*h+2:ℕ)<δ := by
  let C := finitePolynomialErrorFactor A hN P r s hs n
  have hC : 0≤C := finitePolynomialErrorFactor_nonneg A hN P r s hs n
  have hC1 : 0<1+C := by linarith
  have hδ' : 0<δ/(1+C) := div_pos hδ hC1
  obtain ⟨d,I,hI,_⟩ := AsymptoticSharedApproximation.finite_reconstruction_approximation A hN
    (parameters A P) (parameters_bound A P).le hδ'
  refine ⟨d,I,?_⟩
  intro h e Y
  have hh := hI ⟨multiplier e,fun q _ => multiplier_norm e q⟩ (h+1)
  apply (finiteCutPolynomialTrace_normalized_error A hN P r s hs h e Y n d I).trans_lt
  have hb := mul_le_mul_of_nonneg_left hh.le hC
  have he : (1+C)*(δ/(1+C))=δ := mul_div_cancel₀ δ hC1.ne'
  nlinarith

#print axioms finiteCutNormal_norm_le
#print axioms finitePolynomialErrorFactor_nonneg
#print axioms finiteCutPolynomialTrace_normalized_error
#print axioms finiteCutPolynomialTrace_approximation

end AsymptoticCylinderObservation
