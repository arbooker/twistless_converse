module

public import AsymptoticRegularObservationPositiveFamilyV1
public import AsymptoticRegularTraceSandwichV1
public import AsymptoticSignedCornerV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate
open scoped ENNReal

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The finite-terminal-space expression for the trace. Its diagonal is
integrated as a real function; no positivity of this product is assumed. -/
noncomputable def terminalTraceOperator (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  let R := includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z
  (wholeInverse A hN P r s hs e z).comp (R.adjoint.comp R)

theorem positive_trace_toReal_eq_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    (trace volume (positive A hN P r s hs e)).toReal=
      signedTrace volume (terminalTraceOperator A hN P r s hs e) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1/2 :=
    parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q)
  have hk1 : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 :=
    fun z => lt_trans (hk z) (by norm_num)
  have he := funext (positive_eq_whole A hN P r s hs e)
  calc
    _ = signedTrace volume (positive A hN P r s hs e) :=
      (signedTrace_eq_toReal volume _ (positive_matrix_measurable A hN P r s hs e 1 1)
        (positive_isPositive A hN P r s hs e)).symm
    _ = signedTrace volume (fun z => (includedFull A hN P' (multiplier e) z).comp
        ((wholeInverse A hN P r s hs e z).comp (includedFull A hN P' (multiplier e) z).adjoint)) :=
      congrArg (signedTrace volume) he
    _ = _ := signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving _ _
      (includedFull_matrix_measurable A hN P' (multiplier e) hk1)
      (wholeInverse_matrix_measurable A hN P r s hs e)
      (includedFull_covariant A hN P' (multiplier e) hk1)
      (wholeInverse_covariant A hN P r s hs e)
      (includedFull_gram_trace_finite A hN P' (multiplier e) (fun q _ => multiplier_norm e q) hk)
      (wholeInverse_norm_le A hN P r s hs e)

set_option maxHeartbeats 800000 in
theorem terminalTraceOperator_right_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    (terminalTraceOperator A hN P r s hs e z).comp
      (highProjection A (AsymptoticReconstructedCount.parameters A P) z)=terminalTraceOperator A hN P r s hs e z :=
  congrArg (fun T : Space →L[ℂ] Space => (wholeInverse A hN P r s hs e z).comp
    ((includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z).adjoint.comp T))
    (includedFull_right_terminal A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z)

theorem terminalTraceOperator_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    ‖terminalTraceOperator A hN P r s hs e z‖≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := includedFull A hN P' (multiplier e) z
  have hn := includedFull_norm_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) z
    (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (wholeInverse_norm_le A hN P r s hs e z) (norm_nonneg (R.adjoint.comp R))).trans
  rw [one_mul,norm_adjoint_comp_self]
  simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg R) hn 2

theorem terminalTraceOperator_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (terminalTraceOperator A hN P r s hs e z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := includedFull_matrix_measurable A hN P' (multiplier e) hk
  apply matrix_comp_measurable _ _ (wholeInverse_matrix_measurable A hN P r s hs e)
  intro c d
  exact matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm c d

theorem terminalTraceOperator_diagonal_integrable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Integrable (fun z => (matrix (terminalTraceOperator A hN P r s hs e z) 1 1).re) volume := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have harea : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hf : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)<∞ :=
    harea.trans_lt ENNReal.ofReal_lt_top
  exact corner_diagonal_integrable volume (AsymptoticCertificateOperators.highStrip_measurable P'.ε) hf
    (terminalTraceOperator A hN P r s hs e) (terminalTraceOperator_matrix_measurable A hN P r s hs e 1 1)
    (terminalTraceOperator_norm_le A hN P r s hs e) (terminalTraceOperator_right_terminal A hN P r s hs e)

theorem terminal_signedTrace_bound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    ‖signedTrace volume (terminalTraceOperator A hN P r s hs e)‖≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2/
        (AsymptoticReconstructedCount.parameters A P).ε := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have harea : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hf : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)<∞ :=
    harea.trans_lt ENNReal.ofReal_lt_top
  have hb := norm_signedTrace_le_corner volume (AsymptoticCertificateOperators.highStrip_measurable P'.ε) hf
    (terminalTraceOperator A hN P r s hs e) (terminalTraceOperator_norm_le A hN P r s hs e)
    (terminalTraceOperator_right_terminal A hN P r s hs e)
  rw [harea,ENNReal.toReal_ofReal (inv_nonneg.mpr P'.epsilon_pos.le)] at hb
  simpa only [div_eq_mul_inv] using hb

#print axioms terminalTraceOperator_diagonal_integrable
#print axioms terminal_signedTrace_bound

#print axioms positive_trace_toReal_eq_terminal
#print axioms terminalTraceOperator_right_terminal
#print axioms terminalTraceOperator_norm_le
#print axioms terminalTraceOperator_matrix_measurable

end AsymptoticRegularObservation
