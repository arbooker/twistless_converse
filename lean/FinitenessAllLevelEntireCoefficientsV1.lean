module

public import FinitenessAllLevelRegularDegreeV1
public import FinitenessAllLevelSymmetricBoundsV1
public import FinitenessAllLevelCodiscreteExtensionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The symmetric fiber coefficients extend over all exceptional values
as entire functions with explicit polynomial growth. Their values at an
exceptional parameter need not equal the product over the reduced fiber
there; the extension correctly retains limiting multiplicities. -/
theorem entire_fiber_coefficients (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (hf : ∀ w, {x | R w x}.Finite) (hreg : regularValues R ∈ codiscrete ℂ)
    (b : X →L[ℂ] ℂ) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hb : ∀ z x, R z x → ‖b x‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∃ D : ℕ, ∃ a : ℕ → ℂ → ℂ,
      (∀ z ∈ regularValues R, Nat.card {x | R z x} = D) ∧
      (∀ n, Differentiable ℂ (a n)) ∧
      (∀ n, EqOn (a n) (fun z => (fiberPolynomial R b z).coeff n) (regularValues R)) ∧
      ∀ n z, ‖a n z‖ ≤ ((D.choose n : ℝ) * C ^ D) * (1 + ‖z‖) ^ (k * D) := by
  obtain ⟨D, hD⟩ := regular_degree R hp hf hreg
  have he n := codiscrete_entire_extension hreg (fun z => (fiberPolynomial R b z).coeff n)
    (fun z hz => fiberPolynomial_analytic_coeff R hp b z (hf z) hz n)
    (show 0 ≤ (D.choose n : ℝ) * C ^ D by positivity) (k * D)
    (fun z hz => fiberPolynomial_coeff_growth R b z (hf z) D k (hD z hz) hC (hb z) n)
  choose a ha heq hbnd using he
  exact ⟨D, a, hD, ha, heq, hbnd⟩

/-- A genuine monic relation on every regular actual fiber, with entire
coefficient functions of polynomial growth. Obtaining polynomial rather
than entire coefficients is the remaining Liouville step. -/
theorem entire_monic_relation (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (hf : ∀ w, {x | R w x}.Finite) (hreg : regularValues R ∈ codiscrete ℂ)
    (b : X →L[ℂ] ℂ) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hb : ∀ z x, R z x → ‖b x‖ ≤ C * (1 + ‖z‖) ^ k) :
    ∃ D : ℕ, ∃ a : ℕ → ℂ → ℂ,
      (∀ z ∈ regularValues R, Nat.card {x | R z x} = D) ∧
      (∀ n, Differentiable ℂ (a n)) ∧
      (∀ n z, ‖a n z‖ ≤ ((D.choose n : ℝ) * C ^ D) * (1 + ‖z‖) ^ (k * D)) ∧
      ∀ z ∈ regularValues R, a D z = 1 ∧
        ∀ x, R z x → ∑ n ∈ Finset.range (D + 1), a n z * (b x) ^ n = 0 := by
  obtain ⟨D, a, hD, ha, heq, hbnd⟩ := entire_fiber_coefficients R hp hf hreg b hC k hb
  refine ⟨D, a, hD, ha, hbnd, fun z hz => ?_⟩
  have hpoly := fiberPolynomial_monic_degree R b z (hf z)
  have hdeg : (fiberPolynomial R b z).natDegree = D := hpoly.2.trans (hD z hz)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [heq D hz, ← hdeg]
    exact hpoly.1
  · have hzero := fiberPolynomial_eval_zero R b z (hf z) hx
    conv_lhs at hzero => rw [(fiberPolynomial R b z).as_sum_range_C_mul_X_pow]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, hdeg] at hzero
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro n _
    rw [heq n hz]

#print axioms entire_fiber_coefficients
#print axioms entire_monic_relation

end FinitenessAllLevelPolynomialPresentation
