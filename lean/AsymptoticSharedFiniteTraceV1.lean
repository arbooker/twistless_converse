module

public import AsymptoticCylinderFinitePolynomialV1
public import AsymptoticRegularFinitePolynomialTraceV1
public import AsymptoticCylinderCutTraceLimitV1
public import AsymptoticRegularCutTraceLimitV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSharedApproximation

open UpperHalfPlane MeasureTheory Set Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticReconstructedCount AsymptoticRegularTrace
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

private theorem normalized_triangle_lt {a b c k δ : ℝ} (hk : 0<k)
    (h₁ : ‖a-b‖/k<δ/2) (h₂ : ‖b-c‖/k<δ/2) : ‖a-c‖/k<δ := by
  have ht := div_le_div_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub a b c) hk.le
  rw [add_div] at ht
  exact ht.trans_lt ((add_lt_add h₁ h₂).trans_eq (add_halves δ))

/-- One finite reconstruction expression approximates the two actual
polynomial traces simultaneously. The degree and both representation
coefficients remain identical, and weight is not used to make a choice. -/
theorem polynomial_traces_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ d : ℕ,∃ I : Finset ℤ,
      (∀ h : ℕ,∀ e : Sector N,∀ Y : ℝ,
        ‖AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
          AsymptoticCylinderObservation.cutPolynomialTrace A hN P r s hs h e Y n‖/(2*h+2:ℕ)<δ) ∧
      (∀ e : Sector N,∀ Y : ℝ,Y≤(parameters A P).ε →
        ‖signedTrace volume (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
          signedTrace volume (AsymptoticRegularObservation.cutPolynomialTerminal A hN P r s hs e Y n)‖<δ) := by
  let ε := (parameters A P).ε
  let CH := AsymptoticCylinderObservation.finitePolynomialErrorFactor A hN P r s hs n
  let CR := AsymptoticRegularObservation.finitePolynomialErrorFactor A hN P r s hs n
  have hε : 0<ε := (parameters A P).epsilon_pos
  have hCH : 0≤CH := AsymptoticCylinderObservation.finitePolynomialErrorFactor_nonneg A hN P r s hs n
  have hCR : 0≤CR := AsymptoticRegularObservation.finitePolynomialErrorFactor_nonneg A hN P r s hs n
  have hCRε : 0≤CR/ε := div_nonneg hCR hε.le
  let D := 1+CH+CR/ε
  have hD : 0<D := by dsimp [D]; linarith
  let η := δ/D
  have hη : 0<η := div_pos hδ hD
  have he : D*η=δ := mul_div_cancel₀ δ hD.ne'
  obtain ⟨d,I,hH,hR⟩ := finite_reconstruction_approximation A hN (parameters A P) (parameters_bound A P).le hη
  refine ⟨d,I,?_,?_⟩
  · intro h e Y
    apply (AsymptoticCylinderObservation.finiteCutPolynomialTrace_normalized_error A hN P r s hs h e Y n d I).trans_lt
    have hb := mul_le_mul_of_nonneg_left (hH ⟨multiplier e,fun q _ => multiplier_norm e q⟩ (h+1)).le hCH
    dsimp [D] at he
    nlinarith
  · intro e Y hY
    have hd : ∀ z,‖AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I z-
        AsymptoticRegularObservation.cutPolynomialTerminal A hN P r s hs e Y n z‖≤CR*η := by
      intro z
      exact (AsymptoticRegularObservation.finiteCutPolynomialTerminal_error A hN P r s hs e Y n d I z).trans
        (mul_le_mul_of_nonneg_left (hR ⟨multiplier e,fun q _ => multiplier_norm e q⟩ z).le hCR)
    apply (AsymptoticRegularObservation.finiteCutPolynomialTrace_error A hN P r s hs e Y hY n d I hd).trans_lt
    change CR*η/ε<δ
    have hr : CR*η/ε=(CR/ε)*η := by ring
    rw [hr]
    dsimp [D] at he
    nlinarith

/-- The finite inverse degree, reconstruction depth and fold set can
all be chosen in common for the two positive traces, before varying
weight or sector. -/
theorem cutoff_positive_traces_approximation (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) (hY : Y≤(parameters A P).ε)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ n d : ℕ,∃ I : Finset ℤ,
      (∀ h : ℕ,∀ e : Sector N,
        ‖AsymptoticCylinderObservation.finiteCutPolynomialTrace A hN P r s hs h e Y n d I-
          AsymptoticCylinderObservation.cutHolomorphicTrace A hN P r s hs h e Y hY‖/(2*h+2:ℕ)<δ) ∧
      (∀ e : Sector N,
        ‖signedTrace volume (AsymptoticRegularObservation.finiteCutPolynomialTerminal A hN P r s hs e Y n d I)-
          (trace volume (AsymptoticRegularObservation.cutPositive A hN P r s hs e Y)).toReal‖<δ) := by
  have hh := AsymptoticCylinderObservation.cutPolynomialTrace_tendstoUniformly A hN P r s hs Y hY
  have hr := AsymptoticRegularObservation.cutPolynomialTrace_tendstoUniformly A hN P r s hs Y hY
  obtain ⟨n,hnH,hnR⟩ := (((Metric.tendstoUniformly_iff.mp hh) (δ/2) (half_pos hδ)).and
    ((Metric.tendstoUniformly_iff.mp hr) (δ/2) (half_pos hδ))).exists
  obtain ⟨d,I,hdH,hdR⟩ := polynomial_traces_approximation A hN P r s hs n (half_pos hδ)
  refine ⟨n,d,I,?_,?_⟩
  · intro h e
    have hk : (0:ℝ)<(2*h+2:ℕ) := by positivity
    have hp : ‖AsymptoticCylinderObservation.cutPolynomialTrace A hN P r s hs h e Y n-
        AsymptoticCylinderObservation.cutHolomorphicTrace A hN P r s hs h e Y hY‖/(2*h+2:ℕ)<δ/2 := by
      simpa only [dist_eq_norm,← sub_div,norm_div,Real.norm_of_nonneg hk.le,norm_sub_rev] using hnH (h,e)
    exact normalized_triangle_lt hk (hdH h e Y) hp
  · intro e
    have hp : ‖signedTrace volume (AsymptoticRegularObservation.cutPolynomialTerminal A hN P r s hs e Y n)-
        (trace volume (AsymptoticRegularObservation.cutPositive A hN P r s hs e Y)).toReal‖<δ/2 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hnR e
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (signedTrace volume (AsymptoticRegularObservation.cutPolynomialTerminal A hN P r s hs e Y n)) _).trans_lt
      ((add_lt_add (hdR e Y hY) hp).trans_eq (add_halves δ))

#print axioms polynomial_traces_approximation
#print axioms cutoff_positive_traces_approximation

end AsymptoticSharedApproximation
