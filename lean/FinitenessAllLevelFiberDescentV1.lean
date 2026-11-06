module

public import FinitenessAllLevelFiniteFiberAlgebraV1
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Descent

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

open MvPolynomial TensorProduct

/-- Scalar extension commutes with a polynomial fiber quotient. -/
def fiberBaseChange {K : Type*} [Field K] [Algebra K ℂ] {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) :
    ℂ ⊗[K] (MvPolynomial σ K ⧸ I) ≃ₐ[ℂ]
      MvPolynomial σ ℂ ⧸ I.map (MvPolynomial.map (algebraMap K ℂ)) := by
  let e : ℂ ⊗[K] MvPolynomial σ K ≃ₐ[ℂ] MvPolynomial σ ℂ :=
    MvPolynomial.algebraTensorAlgEquiv K ℂ
  have he : (e : (ℂ ⊗[K] MvPolynomial σ K) →+* MvPolynomial σ ℂ).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := ℂ)).toRingHom =
        MvPolynomial.map (algebraMap K ℂ) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[K] p) = MvPolynomial.map (algebraMap K ℂ) p
    simp only [e, algebraTensorAlgEquiv_tmul, one_smul]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := K) ℂ (MvPolynomial σ K) ℂ I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  rw [← he]
  exact (Ideal.map_map _ _).symm

/-- Finite complex fibers descend to any coefficient field embedded in ℂ.
This makes generic specialization useful without falsely assuming that the
specialized coefficient field is algebraically closed. -/
theorem finiteDimensional_descent {K : Type*} [Field K] [Algebra K ℂ]
    {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : (zeroLocus ℂ (I.map (MvPolynomial.map (algebraMap K ℂ)))).Finite) :
    FiniteDimensional K (MvPolynomial σ K ⧸ I) := by
  let := finiteDimensional_quotient _ hI
  let e := fiberBaseChange I
  let : Module.Finite ℂ (ℂ ⊗[K] (MvPolynomial σ K ⧸ I)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ

#print axioms fiberBaseChange
#print axioms finiteDimensional_descent

end FinitenessAllLevelFiniteFiberAlgebra
