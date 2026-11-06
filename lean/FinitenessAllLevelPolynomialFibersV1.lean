module

public import FinitenessAllLevelFiniteFiberAlgebraV1
public import FinitenessAllLevelQuadraticCoordinatesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelQuadraticCoordinates

open Complex Set Module MvPolynomial

/-- The actual degree-two coordinate expression as a multivariate polynomial. -/
def polynomial {n : ℕ} (c : Coeff n) : MvPolynomial (Fin n) ℂ :=
  C c.1 + ∑ i, C (c.2.1 i) * X i + ∑ i, ∑ j, C (c.2.2 i j) * X i * X j

theorem aeval_polynomial {n : ℕ} (c : Coeff n) (v : Fin n → ℂ) :
    aeval v (polynomial c) = evaluate v c := by
  simp [polynomial, evaluate]

/-- Any represented family is a genuine polynomial family, with the same
zero set in every fiber. No radical or extra pointwise conditions are added. -/
theorem representable_polynomials {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (b : Basis (Fin n) ℂ E) {U : Set ℂ}
    (H : ι → ℂ × E → ℂ) (hH : ∀ i, Representable b (U := U) (H i)) :
    ∃ c : ι → ℂ → Coeff n, (∀ i, AnalyticOnNhd ℂ (c i) U) ∧
      ∀ z, zeroLocus ℂ (Ideal.span (range (fun i => polynomial (c i z)))) =
        {x | ∀ i, H i (z, b.equivFun.symm x) = 0} := by
  classical
  choose c hc he using hH
  refine ⟨c, hc, fun z => ?_⟩
  rw [zeroLocus_span]
  ext x
  simp only [mem_ofPred_eq, forall_mem_range, aeval_polynomial]
  have he' (i : ι) : evaluate x (c i z) = H i (z, b.equivFun.symm x) := by
    have hh := he i z (b.equivFun.symm x)
    change evaluate (b.equivFun (b.equivFun.symm x)) (c i z) = _ at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh
  simp only [he']

/-- Finiteness of the actual represented zero set implies finiteness of its
full coordinate algebra; this includes all nilpotent multiplicities. -/
theorem finiteDimensional_represented_fiber {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (b : Basis (Fin n) ℂ E) (H : ι → E → ℂ) (c : ι → Coeff n)
    (hc : ∀ i v, evaluate (b.repr v) (c i) = H i v)
    (hf : {v | ∀ i, H i v = 0}.Finite) :
    FiniteDimensional ℂ
      (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (range (fun i => polynomial (c i)))) := by
  apply FinitenessAllLevelFiniteFiberAlgebra.finiteDimensional_quotient
  apply (hf.image b.equivFun).subset
  intro x hx
  refine ⟨b.equivFun.symm x, ?_, b.equivFun.apply_symm_apply x⟩
  intro i
  have hp : polynomial (c i) ∈ Ideal.span (range (fun i => polynomial (c i))) :=
    Ideal.subset_span (mem_range_self i)
  have he := hx _ hp
  rw [aeval_polynomial] at he
  rw [← hc]
  change evaluate (b.equivFun (b.equivFun.symm x)) (c i) = 0
  simpa only [LinearEquiv.apply_symm_apply] using he

#print axioms aeval_polynomial
#print axioms representable_polynomials
#print axioms finiteDimensional_represented_fiber

end FinitenessAllLevelQuadraticCoordinates
