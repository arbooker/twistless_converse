module

public import FinitenessAllLevelPresentationCoefficientRingV1
public import FinitenessAllLevelSectorPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

def Presentation.restrict (c : Presentation ι R) (V : Set ℂ) (hV : IsOpen V) (hVU : V ⊆ c.U) :
    Presentation ι R := {
  c with
  U := V
  openU := hV
  analytic_lift := c.analytic_lift.mono hVU
  analytic_coefficients := fun j => (c.analytic_coefficients j).mono hVU
  exact_locus := fun z hz x => c.exact_locus z (hVU hz) x }

theorem Presentation.connected_restriction (c : Presentation ι R) {w : ℂ} (hw : w ∈ c.U) :
    ∃ d : Presentation ι R, w ∈ d.U ∧ IsPreconnected d.U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp c.openU w hw
  exact ⟨c.restrict (Metric.ball w ε) Metric.isOpen_ball hsub,
    Metric.mem_ball_self hε, (convex_ball w ε).isPreconnected⟩

#print axioms Presentation.connected_restriction

end FinitenessAllLevelPolynomialPresentation

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelGlobalHeight FinitenessAllLevelPolynomialPresentation
  FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
  QuantitativeArithmeticRetainedCertificate

/-- At every eigenvalue the ACTUAL sector has a connected polynomial chart
whose coordinates satisfy analytic-family eliminating polynomials. The same
eliminant works throughout the chart and has nonzero leading coefficient as
an analytic function. This is stronger than pointwise finite fiber algebra. -/
theorem sector_analytic_eliminants {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    ∃ (d : ℕ) (es : Finset (Index N Q)),
      ∃ c : Presentation (Fin d ⊕ es)
        (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s),
        w ∈ c.U ∧ IsPreconnected c.U ∧ ∀ i : Fin c.n,
          ∃ q : Polynomial (ring c.U c.coefficientFunctions), q ≠ 0 ∧
            (∀ j, AnalyticOnNhd ℂ (representative c.U c.coefficientFunctions (q.coeff j)) c.U) ∧
            (¬ EqOn (representative c.U c.coefficientFunctions q.leadingCoeff) 0 c.U) ∧
            ∀ z : c.U, ∀ v, (∀ j, evaluate v (c.coefficients j z) = 0) →
              q.eval₂ (evaluation c.U c.coefficientFunctions z) (v i) = 0 := by
  obtain ⟨d, es, c, hw⟩ := sector_polynomial_presentation hN hp A P hb hba hae m s w
  obtain ⟨c', hw', hc'⟩ := c.connected_restriction hw
  exact ⟨d, es, c', hw', hc', fun i => c'.coordinate_eliminant hc' ⟨w, hw'⟩
    (fun z => global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z) i⟩

#print axioms sector_analytic_eliminants

end FinitenessAllLevelConstraintLocus
