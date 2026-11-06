module

public import FinitenessAllLevelEntireCoefficientsV1
public import FinitenessAllLevelPolynomialLiouvilleV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The product of all observable values over a regular fiber is the norm
of ONE polynomial in the base parameter. Limiting multiplicities at the
exceptional parameters are supplied by the entire extension. -/
theorem determinant_polynomial (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (hf : ∀ w, {x | R w x}.Finite) (hreg : regularValues R ∈ codiscrete ℂ)
    (b : X →L[ℂ] ℂ) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hb : ∀ z x, R z x → ‖b x‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∃ D : ℕ, ∃ P : Polynomial ℂ,
      (∀ z ∈ regularValues R, Nat.card {x | R z x} = D) ∧
      ∀ z ∈ regularValues R, ‖P.eval z‖ = ∏ᶠ x : {x | R z x}, ‖b x.val‖ := by
  classical
  obtain ⟨D, a, hD, ha, heq, hbnd⟩ := entire_fiber_coefficients R hp hf hreg b hC k hb
  obtain ⟨P, hP⟩ := polynomial_of_entire_growth (a 0) (ha 0)
    (show 0 ≤ (D.choose 0 : ℝ) * C ^ D by positivity) (k * D) (hbnd 0)
  refine ⟨D, P, hD, fun z hz => ?_⟩
  let := (hf z).fintype
  rw [hP z, heq 0 hz]
  simp only [fiberPolynomial, finprod_eq_prod_of_fintype, Polynomial.coeff_zero_prod,
    Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
    norm_prod, norm_neg]

#print axioms determinant_polynomial

end FinitenessAllLevelPolynomialPresentation
