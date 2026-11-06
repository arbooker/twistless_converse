module

public import AsymptoticRegularInversePolynomialV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap Filter AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate
open scoped ENNReal Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def cutPolynomialTerminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  let R := cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z
  (cutInversePolynomial A hN P r s hs e Y n z).comp (R.adjoint.comp R)

set_option maxHeartbeats 800000 in
theorem cutPolynomialTerminal_right_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ) (z : ℍ) :
    (cutPolynomialTerminal A hN P r s hs e Y n z).comp
      (highProjection A (AsymptoticReconstructedCount.parameters A P) z)=cutPolynomialTerminal A hN P r s hs e Y n z :=
  congrArg (fun T : Space →L[ℂ] Space => (cutInversePolynomial A hN P r s hs e Y n z).comp
    ((cutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z).adjoint.comp T))
    (cutFull_right_terminal A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y z)

theorem cutPolynomialTerminal_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutPolynomialTerminal A hN P r s hs e Y n z) a b) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hk : ∀ z,‖low A hN P' (multiplier e) (P'.s+3) z‖<1 := fun z =>
    lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)
  have hm := cutFull_matrix_measurable A hN P' (multiplier e) Y hk
  exact matrix_comp_measurable _ _ (cutInversePolynomial_matrix_measurable A hN P r s hs e Y n)
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm) a b

theorem cutPolynomialTerminal_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n : ℕ) (z : ℍ) :
    ‖cutPolynomialTerminal A hN P r s hs e Y n z-cutTerminalTraceOperator A hN P r s hs e Y z‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n*
        (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := cutFull A hN P' (multiplier e) Y z
  have hn := cutFull_norm_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) Y z
    (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z)
  have he : cutPolynomialTerminal A hN P r s hs e Y n z-cutTerminalTraceOperator A hN P r s hs e Y z=
      (cutInversePolynomial A hN P r s hs e Y n z-cutInverse A hN P r s hs e Y z).comp (R.adjoint.comp R) := by
    exact (sub_comp _ _ _).symm
  rw [he]
  have herr := cutInversePolynomial_error A hN P r s hs e Y hY n z
  have hg : ‖R.adjoint.comp R‖≤(1+2*AsymptoticCertificateOperators.terminalConstant A P')^2 := by
    rw [norm_adjoint_comp_self]
    simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg R) hn 2
  apply (opNorm_comp_le _ _).trans
  exact mul_le_mul herr hg (norm_nonneg _) ((norm_nonneg
    (cutInversePolynomial A hN P r s hs e Y n z-cutInverse A hN P r s hs e Y z)).trans herr)

theorem cutPolynomialTerminal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n : ℕ) (z : ℍ) :
    ‖cutPolynomialTerminal A hN P r s hs e Y n z‖≤
      (polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n+1)*
        (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  have he := cutPolynomialTerminal_error A hN P r s hs e Y hY n z
  have hb := cutTerminalTraceOperator_norm_le A hN P r s hs e Y hY z
  have ht := norm_add_le
    (cutPolynomialTerminal A hN P r s hs e Y n z-cutTerminalTraceOperator A hN P r s hs e Y z)
    (cutTerminalTraceOperator A hN P r s hs e Y z)
  rw [sub_add_cancel] at ht
  exact ht.trans ((add_le_add he hb).trans_eq (by ring))

/-- Finite terminal area converts polynomial inverse error to actual
regular trace error, uniformly in sector. -/
theorem cutPolynomialTrace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n : ℕ) :
    ‖signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n)-
      (trace volume (cutPositive A hN P r s hs e Y)).toReal‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n*
        (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2/
          (AsymptoticReconstructedCount.parameters A P).ε := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have ha : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hf : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)<∞ := ha.trans_lt ENNReal.ofReal_lt_top
  rw [cutPositive_trace_toReal_eq_terminal A hN P r s hs e Y hY]
  have hb := norm_signedTrace_sub_le_corner volume
    (AsymptoticCertificateOperators.highStrip_measurable P'.ε) hf
    (cutPolynomialTerminal A hN P r s hs e Y n) (cutTerminalTraceOperator A hN P r s hs e Y)
    (cutPolynomialTerminal_matrix_measurable A hN P r s hs e Y n 1 1)
    (cutTerminalTraceOperator_matrix_measurable A hN P r s hs e Y hY 1 1)
    (cutPolynomialTerminal_norm_le A hN P r s hs e Y hY n) (cutTerminalTraceOperator_norm_le A hN P r s hs e Y hY)
    (cutPolynomialTerminal_right_terminal A hN P r s hs e Y n) (cutTerminalTraceOperator_right_terminal A hN P r s hs e Y)
    (cutPolynomialTerminal_error A hN P r s hs e Y hY n)
  rw [ha,ENNReal.toReal_ofReal (inv_nonneg.mpr P'.epsilon_pos.le)] at hb
  simpa only [div_eq_mul_inv] using hb

theorem cutPolynomialTrace_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    TendstoUniformly (fun n (e : Sector N) => signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n))
      (fun e : Sector N => (trace volume (cutPositive A hN P r s hs e Y)).toReal) atTop := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A P'
  have hd : Tendsto (fun n => polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n*BR^2/P'.ε) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_div] using
      ((polynomialError_tendsto_zero (AsymptoticSharedApproximation.normalBound A hN P r s hs)).mul_const (BR^2)).div_const P'.ε
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn e
  rw [dist_eq_norm,norm_sub_rev]
  exact (cutPolynomialTrace_error A hN P r s hs e Y hY n).trans_lt hn

#print axioms cutPolynomialTerminal_right_terminal
#print axioms cutPolynomialTerminal_matrix_measurable
#print axioms cutPolynomialTerminal_error
#print axioms cutPolynomialTerminal_norm_le
#print axioms cutPolynomialTrace_error
#print axioms cutPolynomialTrace_tendstoUniformly

end AsymptoticRegularObservation
