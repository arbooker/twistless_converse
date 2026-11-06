module

public import FinitenessAllLevelConstraintLocusV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCauchyConstraints FinitenessAllLevelFunctionalChart
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

/-- All spatial side conditions are carried by the index, so every equation
has one common parameter domain. -/
inductive Index (N Q : ℕ) where
  | cauchy (c w : ℂ) (R : ℝ) (hR : 0 < R) (hRc : R < c.im) (hw : w ∈ ball c R)
  | fricke (q : ℕ) (hq : q ∣ Q) (z : ℂ) (hz : 0 < z.im)
  | hecke (z : ℂ) (hz : 0 < z.im)
  | euler (e : FinitenessAllLevelEulerEquations.Equation N)

variable {N Q p : ℕ} {hQ : 0 < Q}

def scalar (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (e : Index N Q) (t : ℂ × space (radius a)) : ℂ :=
  let G := formal A P a χ m t.1 t.2
  match e with
  | .cauchy c w R _ _ _ => transform c R G w - G w
  | .fricke q _ z _ => twist G q z -
      χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m) *
        twist G q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z))
  | .hecke z _ => completeTwist G p z -
      (firstMultiplier (fun _ => t.1) m p * G ((p : ℂ) * z) -
        (p : ℂ) ^ (2 * m) * G ((p : ℂ) ^ 2 * z))
  | .euler e => FinitenessAllLevelEulerEquations.equation N (2 * m) p (radius_pos a) e t

theorem scalar_zero_iff (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    (∀ e : Index N Q, scalar A P a χ m e (lam, F) = 0) ↔ Constraints A P a χ m lam F := by
  constructor
  · intro he
    exact ⟨fun c R hR hRc w hw => sub_eq_zero.mp (he (.cauchy c w R hR hRc hw)),
      fun q hq z hz => sub_eq_zero.mp (he (.fricke q hq z hz)),
      fun z hz => sub_eq_zero.mp (he (.hecke z hz)), fun e => he (.euler e)⟩
  · intro he e
    cases e with
    | cauchy c w R hR hRc hw => exact sub_eq_zero.mpr (he.cauchy c R hR hRc w hw)
    | fricke q hq z hz => exact sub_eq_zero.mpr (he.fricke q hq z hz)
    | hecke z hz => exact sub_eq_zero.mpr (he.hecke z hz)
    | euler e => exact he.euler e

/-- Every member of the full exact equation system is analytic on the
same finite-dimensional Fredholm chart domain. -/
theorem scalar_chart_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (e : Index N Q)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set ℂ} (hU : IsOpen U) {J : ℂ → E →L[ℂ] space (radius a)}
    (hJ : AnalyticOnNhd ℂ J U) :
    AnalyticOnNhd ℂ (fun t : ℂ × E => scalar A P a χ m e (t.1, J t.1 t.2))
      (U ×ˢ univ) := by
  cases e with
  | cauchy c w R hR hRc hw =>
      exact equation_chart_analytic hN hp A P ha hae χ m hR hRc hw hU hJ
  | fricke q hq z hz => exact fricke_analytic A P a χ m q z hJ
  | hecke z hz => exact hecke_analytic A P a χ m z hJ
  | euler e => exact FinitenessAllLevelEulerEquations.chart_equations N (2 * m) p (radius_pos a) hJ e

#print axioms scalar_zero_iff
#print axioms scalar_chart_analytic

end FinitenessAllLevelConstraintLocus
