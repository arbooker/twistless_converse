module

public import AsymptoticRegularFinitePolynomialV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap Filter AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate
open scoped ENNReal

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem finiteCutPolynomialTerminal_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) : Covariant (finiteCutPolynomialTerminal A hN P r s hs e Y n d I) := by
  have hc := finiteCutFull_covariant A hN (AsymptoticReconstructedCount.parameters A P)
    (multiplier e) Y d I
  exact covariant_comp _ _ (polynomial_covariant _ _ (finiteCutNormal_covariant A hN P r s hs e Y d I) n)
    (covariant_comp _ _ (covariant_adjoint _ hc) hc)

theorem finiteCutPolynomialTerminal_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteCutPolynomialTerminal A hN P r s hs e Y n d I z) a b) := by
  have hm := finiteCutFull_matrix_measurable A hN (AsymptoticReconstructedCount.parameters A P)
    (multiplier e) Y d I
  exact matrix_comp_measurable _ _
    (polynomial_matrix_measurable _ _ (finiteCutNormal_matrix_measurable A hN P r s hs e Y d I) n)
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm) a b

set_option maxHeartbeats 800000 in
theorem finiteCutPolynomialTerminal_right_terminal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    (finiteCutPolynomialTerminal A hN P r s hs e Y n d I z).comp
      (highProjection A (AsymptoticReconstructedCount.parameters A P) z)=
        finiteCutPolynomialTerminal A hN P r s hs e Y n d I z :=
  congrArg (fun T : Space →L[ℂ] Space =>
    (polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs)
      (finiteCutNormal A hN P r s hs e Y d I z) n).comp
      ((finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z).adjoint.comp T))
    (finiteCutFull_right_terminal A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z)

theorem finiteCutPolynomialTerminal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (n d : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteCutPolynomialTerminal A hN P r s hs e Y n d I z‖≤
      polynomialBound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
        (wholeNormalBound A hN P r s hs) n*
          (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
  let R := finiteCutFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) Y d I z
  have hR := finiteCutFull_norm_le A hN _ (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) Y d I z
  have hg : ‖R.adjoint.comp R‖≤
      (1+2*AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P))^2 := by
    rw [norm_adjoint_comp_self]
    simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg R) hR 2
  have hi := polynomial_norm_le_of_bound (AsymptoticSharedApproximation.normalBound A hN P r s hs)
    _ (finiteCutNormal_norm_le A hN P r s hs e Y d I z) n
  exact (opNorm_comp_le _ _).trans (mul_le_mul hi hg (norm_nonneg _) ((norm_nonneg _).trans hi))

/-- Finite terminal area turns the proved operator approximation into
an actual rooted-trace approximation. Both diagonals are measurable and
integrable; no trace on the infinite-area identity is used. -/
theorem finiteCutPolynomialTrace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n d : ℕ) (I : Finset ℤ)
    {δ : ℝ} (hd : ∀ z,‖finiteCutPolynomialTerminal A hN P r s hs e Y n d I z-
      cutPolynomialTerminal A hN P r s hs e Y n z‖≤δ) :
    ‖signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
      signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n)‖≤
        δ/(AsymptoticReconstructedCount.parameters A P).ε := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have ha : (volume : Measure ℍ) (AsymptoticCertificateOperators.highStrip P'.ε)=ENNReal.ofReal P'.ε⁻¹ :=
    AsymptoticHyperbolicArea.closed_terminal_area P'.epsilon_pos
  have hb := norm_signedTrace_sub_le_corner volume
    (AsymptoticCertificateOperators.highStrip_measurable P'.ε) (ha.trans_lt ENNReal.ofReal_lt_top)
    (finiteCutPolynomialTerminal A hN P r s hs e Y n d I) (cutPolynomialTerminal A hN P r s hs e Y n)
    (finiteCutPolynomialTerminal_matrix_measurable A hN P r s hs e Y n d I 1 1)
    (cutPolynomialTerminal_matrix_measurable A hN P r s hs e Y n 1 1)
    (finiteCutPolynomialTerminal_norm_le A hN P r s hs e Y n d I)
    (cutPolynomialTerminal_norm_le A hN P r s hs e Y hY n)
    (finiteCutPolynomialTerminal_right_terminal A hN P r s hs e Y n d I)
    (cutPolynomialTerminal_right_terminal A hN P r s hs e Y n) hd
  rw [ha,ENNReal.toReal_ofReal (inv_nonneg.mpr P'.epsilon_pos.le)] at hb
  simpa only [div_eq_mul_inv] using hb

theorem finiteCutPolynomialTrace_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ d : ℕ,∃ I : Finset ℤ,∀ e : Sector N,∀ Y : ℝ,
      Y≤(AsymptoticReconstructedCount.parameters A P).ε →
      ‖signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
        signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n)‖<δ := by
  let ε := (AsymptoticReconstructedCount.parameters A P).ε
  have hε : 0<ε := (AsymptoticReconstructedCount.parameters A P).epsilon_pos
  obtain ⟨d,I,hI⟩ := finiteCutPolynomialTerminal_approximation A hN P r s hs n
    (mul_pos (half_pos hδ) hε)
  refine ⟨d,I,?_⟩
  intro e Y hY
  have ht := finiteCutPolynomialTrace_error A hN P r s hs e Y hY n d I
    (fun z => (hI e Y z).le)
  have he : (δ/2*ε)/ε=δ/2 := mul_div_cancel_right₀ _ hε.ne'
  exact ht.trans_lt (he.trans_lt (half_lt_self hδ))

/-- A finite polynomial branch expression approximates the actual
regular positive trace. All degree, depth and fold choices are made
before varying the sector. -/
theorem finiteCut_positive_trace_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) {δ : ℝ} (hδ : 0<δ) :
    ∃ n d : ℕ,∃ I : Finset ℤ,∀ e : Sector N,
      ‖signedTrace volume (finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
        (trace volume (cutPositive A hN P r s hs e Y)).toReal‖<δ := by
  have hp := cutPolynomialTrace_tendstoUniformly A hN P r s hs Y hY
  obtain ⟨n,hn⟩ := ((Metric.tendstoUniformly_iff.mp hp) (δ/2) (half_pos hδ)).exists
  obtain ⟨d,I,hI⟩ := finiteCutPolynomialTrace_approximation A hN P r s hs n (half_pos hδ)
  refine ⟨n,d,I,?_⟩
  intro e
  have he : ‖signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n)-
      (trace volume (cutPositive A hN P r s hs e Y)).toReal‖<δ/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hn e
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (signedTrace volume (cutPolynomialTerminal A hN P r s hs e Y n)) _).trans_lt
    ((add_lt_add (hI e Y hY) he).trans_eq (add_halves δ))

#print axioms finiteCutPolynomialTerminal_covariant
#print axioms finiteCutPolynomialTerminal_matrix_measurable
#print axioms finiteCutPolynomialTerminal_right_terminal
#print axioms finiteCutPolynomialTerminal_norm_le
#print axioms finiteCutPolynomialTrace_error
#print axioms finiteCutPolynomialTrace_approximation
#print axioms finiteCut_positive_trace_approximation

end AsymptoticRegularObservation
