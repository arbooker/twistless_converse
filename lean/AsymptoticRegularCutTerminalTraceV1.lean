module

public import AsymptoticRegularCutPositiveV1
public import AsymptoticGramProductPerturbationV1
public import AsymptoticRegularSandwichBoundV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate
open scoped ENNReal

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem cutPositive_trace_finite (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    trace volume (cutPositive A hN P r s hs e Y)<∞ := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1/2 :=
    parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q)
  have hk1 : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z => lt_trans (hk z) (by norm_num)
  have hf := cutFull_gram_trace_finite A hN P' (multiplier e) (fun q _ => multiplier_norm e q) Y hk
  have he := rational_trace_adjoint_mul (cutFull A hN P' (multiplier e) Y)
    (cutFull_matrix_measurable A hN P' (multiplier e) Y hk1) (cutFull_covariant A hN P' (multiplier e) Y hk1)
  exact (trace_sandwich_le_range_gram volume (cutFull A hN P' (multiplier e) Y)
    (cutInverse A hN P r s hs e Y) (cutInverse_norm_le A hN P r s hs e Y hY)).trans_lt (he.symm.trans_lt hf)

noncomputable def cutTerminalTraceOperator (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  let R := cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z
  (cutInverse A hN P r s hs e Y z).comp (R.adjoint.comp R)

theorem cutPositive_trace_toReal_eq_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    (trace volume (cutPositive A hN P r s hs e Y)).toReal=
      signedTrace volume (cutTerminalTraceOperator A hN P r s hs e Y) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1/2 :=
    parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q)
  have hk1 : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z => lt_trans (hk z) (by norm_num)
  exact (signedTrace_eq_toReal volume _ (cutPositive_matrix_measurable A hN P r s hs e Y hY 1 1)
    (cutPositive_isPositive A hN P r s hs e Y hY)).symm.trans
      (signedTrace_sandwich volume AsymptoticRationalGroup.measurePreserving _ _
        (cutFull_matrix_measurable A hN P' (multiplier e) Y hk1)
        (cutInverse_matrix_measurable A hN P r s hs e Y hY)
        (cutFull_covariant A hN P' (multiplier e) Y hk1) (cutInverse_covariant A hN P r s hs e Y hY)
        (cutFull_gram_trace_finite A hN P' (multiplier e) (fun q _ => multiplier_norm e q) Y hk)
        (cutInverse_norm_le A hN P r s hs e Y hY))

set_option maxHeartbeats 800000 in
theorem cutTerminalTraceOperator_right_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) :
    (cutTerminalTraceOperator A hN P r s hs e Y z).comp
      (highProjection A (AsymptoticReconstructedCount.parameters A P) z)=cutTerminalTraceOperator A hN P r s hs e Y z :=
  congrArg (fun T : Space →L[ℂ] Space => (cutInverse A hN P r s hs e Y z).comp
    ((cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z).adjoint.comp T))
    (cutFull_right_terminal A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z)

theorem cutTerminalTraceOperator_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    ‖cutTerminalTraceOperator A hN P r s hs e Y z‖≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := cutFull A hN P' (multiplier e) Y z
  have hn := cutFull_norm_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) Y z
    (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (cutInverse_norm_le A hN P r s hs e Y hY z) (norm_nonneg (R.adjoint.comp R))).trans
  rw [one_mul,norm_adjoint_comp_self]
  simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg R) hn 2

theorem cutTerminalTraceOperator_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutTerminalTraceOperator A hN P r s hs e Y z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := cutFull_matrix_measurable A hN P' (multiplier e) Y hk
  exact matrix_comp_measurable _ _ (cutInverse_matrix_measurable A hN P r s hs e Y hY)
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm) a b

noncomputable def cutTraceErrorBound (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  cutErrorBound A hN P r s hs Y*BR^2+2*BR*(Y/P'.ε*BR)

theorem cutTerminalTraceOperator_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY0 : 0≤Y) (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    ‖terminalTraceOperator A hN P r s hs e z-cutTerminalTraceOperator A hN P r s hs e Y z‖≤
      cutTraceErrorBound A hN P r s hs Y := by
  apply AsymptoticObservation.gram_product_sub_norm_le
  · exact includedFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact cutFull_norm_le A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact cutInverse_norm_le A hN P r s hs e Y hY z
  · exact cutFull_error A hN _ (multiplier e) (fun q _ => multiplier_norm e q) Y hY0 z
      (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  · exact cutInverse_error A hN P r s hs e Y hY0 hY z

#print axioms cutPositive_trace_finite
#print axioms cutPositive_trace_toReal_eq_terminal
#print axioms cutTerminalTraceOperator_right_terminal
#print axioms cutTerminalTraceOperator_norm_le
#print axioms cutTerminalTraceOperator_matrix_measurable
#print axioms cutTerminalTraceOperator_error

end AsymptoticRegularObservation
