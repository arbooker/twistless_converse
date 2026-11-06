module

public import FinitenessAllLevelConstraintQuadraticV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set Metric Module FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelQuadraticCoordinates
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a connected parameter domain the actual infinite constraint system
is locally equivalent to finitely many of its own equations, uniformly in
the finite-dimensional coordinate. No analytic Noetherian axiom is used. -/
theorem finite_constraints_connected (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U)
    {w : ℂ} (hw : w ∈ U) :
    ∃ s : Finset (Index N Q), ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∀ z ∈ V, ∀ v : E, Constraints A P a χ m z (J z v) ↔
        ∀ e ∈ s, scalar A P a χ m e (z, J z v) = 0 := by
  let b := Module.finBasis ℂ E
  obtain ⟨s, V, hVo, hwV, hVU, he⟩ := finite_equations_neighborhood b hU hconn
    (fun e (t : ℂ × E) => scalar A P a χ m e (t.1, J t.1 t.2))
    (fun e => scalar_representable hN hp A P ha hae χ m e b hU hJ) hw
  exact ⟨s, V, hVo, hwV, hVU, fun z hz v =>
    (scalar_zero_iff A P a χ m z (J z v)).symm.trans (he z hz v)⟩

/-- Every point of any common open chart domain has an open neighborhood
where finitely many actual holomorphic equations define the exact constraints. -/
theorem finite_constraints_local (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {U : Set ℂ} (hU : IsOpen U)
    {J : ℂ → E →L[ℂ] space (radius a)} (hJ : AnalyticOnNhd ℂ J U)
    {w : ℂ} (hw : w ∈ U) :
    ∃ s : Finset (Index N Q), ∃ V : Set ℂ, IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      (∀ e ∈ s, AnalyticOnNhd ℂ (fun t : ℂ × E =>
        scalar A P a χ m e (t.1, J t.1 t.2)) (V ×ˢ univ)) ∧
      ∀ z ∈ V, ∀ v : E, Constraints A P a χ m z (J z v) ↔
        ∀ e ∈ s, scalar A P a χ m e (z, J z v) = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hw
  obtain ⟨s, V, hVo, hwV, hVB, he⟩ := finite_constraints_connected hN hp A P ha hae χ m
    isOpen_ball (convex_ball w r).isPreconnected (hJ.mono hball) (mem_ball_self hr)
  have hVU := hVB.trans hball
  exact ⟨s, V, hVo, hwV, hVU, fun e _ =>
    (scalar_chart_analytic hN hp A P ha hae χ m e hU hJ).mono
      (prod_mono hVU Subset.rfl), he⟩

#print axioms finite_constraints_connected
#print axioms finite_constraints_local

end FinitenessAllLevelConstraintLocus
