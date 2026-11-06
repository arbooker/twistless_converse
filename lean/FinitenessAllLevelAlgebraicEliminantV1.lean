module

public import FinitenessAllLevelFiberDescentV1
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

open MvPolynomial Set

/-- A finite specialization along an injective coefficient map gives an
eliminating polynomial in each coordinate over the original domain. Its
leading coefficient is nonzero; the relation lies in the original ideal. -/
theorem coordinate_eliminant {A σ : Type*} [CommRing A] [IsDomain A] [Finite σ]
    (e : A →+* ℂ) (he : Function.Injective e) (I : Ideal (MvPolynomial σ A))
    (hI : (zeroLocus ℂ (I.map (MvPolynomial.map e))).Finite) (i : σ) :
    ∃ q : Polynomial A, q ≠ 0 ∧ Polynomial.aeval (X i) q ∈ I := by
  let K := FractionRing A
  let E : K →+* ℂ := IsFractionRing.lift he
  let : Algebra K ℂ := E.toAlgebra
  let J : Ideal (MvPolynomial σ K) := I.map (MvPolynomial.map (algebraMap A K))
  have hmap : (MvPolynomial.map (σ := σ) (algebraMap K ℂ)).comp
      (MvPolynomial.map (algebraMap A K)) = MvPolynomial.map e := by
    have hcomp : (algebraMap K ℂ).comp (algebraMap A K) = e := by
      apply RingHom.ext
      intro a
      exact IsFractionRing.lift_algebraMap he a
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, MvPolynomial.map_map, hcomp]
  have hJ : (zeroLocus ℂ (J.map (MvPolynomial.map (algebraMap K ℂ)))).Finite := by
    simpa only [J, Ideal.map_map, hmap] using hI
  let := finiteDimensional_descent J hJ
  let C := MvPolynomial σ K ⧸ J
  let x : C := Ideal.Quotient.mk J (X i)
  have hx : IsAlgebraic K x := (IsIntegral.of_finite K x).isAlgebraic
  obtain ⟨q, hq, hzero⟩ := (IsFractionRing.isAlgebraic_iff A K C).mpr hx
  let f : MvPolynomial σ A →ₐ[A] C :=
    (Ideal.Quotient.mkₐ A J).comp (MvPolynomial.mapAlgHom (Algebra.ofId A K))
  have hmem : MvPolynomial.map (algebraMap A K) (Polynomial.aeval (X i) q) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (Polynomial.aeval (X i) q) = 0
    rw [← Polynomial.aeval_algHom_apply]
    simpa only [f, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, map_X,
      x, Ideal.Quotient.mkₐ_eq_mk] using hzero
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := K)
  have hmem' : algebraMap (MvPolynomial σ A) (MvPolynomial σ K)
      (Polynomial.aeval (X i) q) ∈ I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)) := hmem
  obtain ⟨s, hs, hsI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (MvPolynomial.C (σ := σ))) (MvPolynomial σ K) I _).mp hmem'
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨Polynomial.C a * q, mul_ne_zero (Polynomial.C_ne_zero.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mp ha)) hq, ?_⟩
  simpa only [map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq] using hsI

#print axioms coordinate_eliminant

end FinitenessAllLevelFiniteFiberAlgebra
