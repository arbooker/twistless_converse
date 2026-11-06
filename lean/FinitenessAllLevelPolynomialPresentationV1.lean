module

public import FinitenessAllLevelPolynomialFibersV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set FinitenessAllLevelQuadraticCoordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An exact presentation by polynomials in finitely many fiber coordinates,
whose coefficients are holomorphic in the eigenvalue. All data are explicit;
no finiteness, normalization or curve theorem is part of the structure. -/
structure Presentation (ι : Type*) (R : ℂ → X → Prop) where
  n : ℕ
  U : Set ℂ
  openU : IsOpen U
  lift : ℂ → (Fin n → ℂ) →L[ℂ] X
  analytic_lift : AnalyticOnNhd ℂ lift U
  injective_lift : ∀ z, Function.Injective (lift z)
  coefficients : ι → ℂ → Coeff n
  analytic_coefficients : ∀ i, AnalyticOnNhd ℂ (coefficients i) U
  exact_locus : ∀ z ∈ U, ∀ x, R z x ↔
    ∃ v, (∀ i, evaluate v (coefficients i z) = 0) ∧ x = lift z v

variable {ι : Type*} {R : ℂ → X → Prop}

def Presentation.fiberIdeal (c : Presentation ι R) (z : ℂ) :
    Ideal (MvPolynomial (Fin c.n) ℂ) :=
  Ideal.span (range (fun i => polynomial (c.coefficients i z)))

theorem Presentation.mem_zeroLocus (c : Presentation ι R) (z : ℂ) (v : Fin c.n → ℂ) :
    v ∈ MvPolynomial.zeroLocus ℂ (c.fiberIdeal z) ↔
      ∀ i, evaluate v (c.coefficients i z) = 0 := by
  simp only [fiberIdeal, MvPolynomial.zeroLocus_span, mem_ofPred_eq,
    forall_mem_range, aeval_polynomial]

/-- The presentation has a finite scheme-theoretic fiber algebra whenever
the actual ambient fiber is finite. -/
theorem Presentation.finiteDimensional_fiber (c : Presentation ι R) {z : ℂ}
    (hz : z ∈ c.U) (hf : {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite) :
    FiniteDimensional ℂ (MvPolynomial (Fin c.n) ℂ ⧸ c.fiberIdeal z) := by
  apply FinitenessAllLevelFiniteFiberAlgebra.finiteDimensional_quotient
  have hinj : Function.Injective (fun v : Fin c.n → ℂ => (z, c.lift z v)) :=
    fun _ _ he => c.injective_lift z (congrArg Prod.snd he)
  apply (Set.Finite.preimage hinj.injOn hf).subset
  intro v hv
  exact ⟨(c.exact_locus z hz _).mpr ⟨v, (c.mem_zeroLocus z v).mp hv, rfl⟩, rfl⟩

#print axioms Presentation.mem_zeroLocus
#print axioms Presentation.finiteDimensional_fiber

end FinitenessAllLevelPolynomialPresentation
