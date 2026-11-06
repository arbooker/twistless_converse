module

public import FinitenessAllLevelFiniteEquationsV1
public import FinitenessAllLevelSpatialLinearV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set Module FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCoefficientFunctional
  FinitenessAllLevelQuadraticCoordinates FinitenessAllLevelAnalyticSubstitution
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The complete exact equation system has degree at most two in chart
coordinates, with coefficient vectors analytic on the common eigenvalue domain. -/
theorem scalar_representable (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (e : Index N Q)
    {n : ℕ} (b : Basis (Fin n) ℂ E)
    {U : Set ℂ} (hU : IsOpen U) {J : ℂ → E →L[ℂ] space (radius a)}
    (hJ : AnalyticOnNhd ℂ J U) :
    Representable b (U := U) (fun t : ℂ × E => scalar A P a χ m e (t.1, J t.1 t.2)) := by
  have hsp (e : Index N Q) (he : e.IsSpatial) :
      Representable b (U := U) (fun t : ℂ × E => scalar A P a χ m e (t.1, J t.1 t.2)) := by
    have hh := represent_linear b
      (fun z => (spatialLinear hN hp A P ha hae χ m e z).comp (J z).toLinearMap)
      (by
        intro v z hz
        have hscalar := scalar_chart_analytic hN hp A P ha hae χ m e hU hJ (z, v) ⟨hz, mem_univ _⟩
        have heq : (fun z => (spatialLinear hN hp A P ha hae χ m e z).comp (J z).toLinearMap v) =
            (fun z => scalar A P a χ m e (z, J z v)) := by
          funext z
          exact spatialLinear_apply hN hp A P ha hae χ m e he z (J z v)
        rw [heq]
        exact hscalar.comp (f := fun z : ℂ => (z, v)) (analyticAt_id.prod analyticAt_const))
    obtain ⟨c, hc, hcEq⟩ := hh
    refine ⟨c, hc, fun z v => ?_⟩
    exact (hcEq z v).trans (spatialLinear_apply hN hp A P ha hae χ m e he z (J z v))
  cases e with
  | cauchy c w R hR hRc hw => exact hsp _ trivial
  | fricke q hq z hz => exact hsp _ trivial
  | hecke z hz => exact hsp _ trivial
  | euler e =>
    let T : ℕ → ℂ → E →ₗ[ℂ] ℂ := fun j z =>
      (normalizedCLM (radius_pos a) (2 * m) j).toLinearMap.comp (J z).toLinearMap
    have hT (j : ℕ) (v : E) : AnalyticOnNhd ℂ (fun z => T j z v) U := by
      intro z hz
      exact ((normalizedCLM (radius_pos a) (2 * m) j).analyticAt _).comp
        ((joint_analytic hJ (z, v) ⟨hz, mem_univ _⟩).comp
          (f := fun z : ℂ => (z, v)) (analyticAt_id.prod analyticAt_const))
    have hlin (j : ℕ) := represent_linear b (T j) (hT j)
    have hprod (i j : ℕ) := represent_product b (T i) (T j) (hT i) (hT j)
    cases e with
    | zero => exact hlin 0
    | one => exact (hlin 1).sub b (represent_constant b analyticOnNhd_const)
    | eigenvalue => exact (hlin p).sub b (represent_constant b analyticOnNhd_id)
    | multiplicative i j hij => exact (hlin (i * j)).sub b (hprod i j)
    | primePower q j hq =>
      exact (hlin (q ^ (j + 2))).sub b ((hprod q (q ^ (j + 1))).sub b
        ((hlin (q ^ j)).const_mul b (if q ∣ N then (0 : ℂ) else 1)))
    | bad q hq hd =>
      simpa only [scalar, FinitenessAllLevelEulerEquations.equation, pow_two,
        T, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
        (hprod q q).sub b (represent_constant b (g := fun _ =>
          if q * q ∣ N then (0 : ℂ) else (q : ℂ)⁻¹) analyticOnNhd_const)

#print axioms scalar_representable

end FinitenessAllLevelConstraintLocus
