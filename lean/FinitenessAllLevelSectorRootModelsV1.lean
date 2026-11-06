module

public import FinitenessAllLevelEliminantBranchesV1
public import FinitenessAllLevelSectorEliminantsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

/-- Proven scalar root models for all chart coordinates at one parameter.
They contain the actual system's zeros. This definition does not assert
that a tuple of scalar root branches satisfies the entire system. -/
def Presentation.RootModel (c : Presentation ι R) (w : c.U) : Prop :=
  ∀ i : Fin c.n, ∃ q : Polynomial (ring c.U c.coefficientFunctions),
    q ≠ 0 ∧ (q.map (evaluation c.U c.coefficientFunctions w)).Separable ∧
    (∀ z : c.U, ∀ v, (∀ j, evaluate v (c.coefficients j z) = 0) →
      polynomialEquation c.coefficientFunctions q (z, v i) = 0) ∧
    ∀ x : ℂ, q.eval₂ (evaluation c.U c.coefficientFunctions w) x = 0 →
      ∃ b : ℂ → ℂ, b w = x ∧ AnalyticAt ℂ b w ∧
        (∀ᶠ z in 𝓝 w.val, polynomialEquation c.coefficientFunctions q (z, b z) = 0) ∧
        ∀ᶠ t in 𝓝 (w.val, x),
          polynomialEquation c.coefficientFunctions q t = 0 ↔ b t.1 = t.2

/-- Every open subdomain has a common parameter with genuine scalar
holomorphic root branches for all actual chart coordinates. -/
theorem Presentation.exists_rootModel [Countable ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite)
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ c.U) (hne : V.Nonempty) :
    ∃ w : c.U, w.val ∈ V ∧ c.RootModel w := by
  obtain ⟨w, hw, he⟩ := generic_separable_eliminants c.coefficientFunctions hconn
    c.coefficientFunctions_analytic c.ringIdeal
    (fun z => by rw [c.map_ringIdeal]; exact c.zeroLocus_finite z.property (hf z)) hV hVU hne
  refine ⟨w, hw, fun i => ?_⟩
  obtain ⟨q, hq, hs, _, hzero⟩ := he i
  refine ⟨q, hq, hs, ?_, fun x hx => eliminant_root_branch c.coefficientFunctions
    c.coefficientFunctions_analytic q w x hs hx⟩
  intro z v hv
  rw [polynomialEquation_eq]
  apply hzero z v
  rw [c.map_ringIdeal]
  exact (c.mem_zeroLocus z v).mpr hv

#print axioms Presentation.exists_rootModel

end FinitenessAllLevelPolynomialPresentation

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelGlobalHeight FinitenessAllLevelPolynomialPresentation
  QuantitativeArithmeticRetainedCertificate

/-- Actual original sectors have generic scalar root models on every
connected chart neighborhood, derived without a normalization or analytic
proper-mapping assumption. Compatibility with the full system remains a
separate obligation. -/
theorem sector_root_models {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) (w : ℂ) :
    ∃ (d : ℕ) (es : Finset (Index N Q)),
      ∃ c : Presentation (Fin d ⊕ es)
        (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s),
        w ∈ c.U ∧ IsPreconnected c.U ∧
        ∀ V : Set ℂ, IsOpen V → V ⊆ c.U → V.Nonempty →
          ∃ z : c.U, z.val ∈ V ∧ c.RootModel z := by
  obtain ⟨d, es, c, hw⟩ := sector_polynomial_presentation hN hp A P hb hba hae m s w
  obtain ⟨c', hw', hc'⟩ := c.connected_restriction hw
  refine ⟨d, es, c', hw', hc', fun V hV hVU hne => ?_⟩
  exact c'.exists_rootModel hc'
    (fun z => global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z)
    hV hVU hne

#print axioms sector_root_models

end FinitenessAllLevelConstraintLocus
