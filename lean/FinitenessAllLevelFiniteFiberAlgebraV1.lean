module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

open MvPolynomial

variable {σ : Type*} [Finite σ]

/-- A finite complex zero set gives a monic relation in each coordinate in
the original ideal, not just in its radical. Multiplicities are retained. -/
theorem coordinate_monic_relation (I : Ideal (MvPolynomial σ ℂ))
    (hI : (zeroLocus ℂ I).Finite) (i : σ) :
    ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (X i) q ∈ I := by
  classical
  let q : Polynomial ℂ := ∏ x ∈ hI.toFinset, (Polynomial.X - Polynomial.C (x i))
  have hq : q.Monic := Polynomial.monic_prod_of_monic _ _
    (fun x _ => Polynomial.monic_X_sub_C (x i))
  have hv : Polynomial.aeval (X i) q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro x hx
    rw [← Polynomial.aeval_algHom_apply]
    simp only [aeval_X]
    simp only [q, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact Finset.prod_eq_zero (hI.mem_toFinset.mpr hx) (sub_self (x i))
  rw [vanishingIdeal_zeroLocus_eq_radical] at hv
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hv
  exact ⟨q ^ n, hq.pow n, by simpa only [map_pow] using hn⟩

/-- Every coordinate in the scheme-theoretic fiber algebra is integral. -/
theorem coordinate_integral (I : Ideal (MvPolynomial σ ℂ))
    (hI : (zeroLocus ℂ I).Finite) (i : σ) :
    IsIntegral ℂ (Ideal.Quotient.mk I (X i)) := by
  obtain ⟨q, hq, hmem⟩ := coordinate_monic_relation I hI i
  refine ⟨q, hq, ?_⟩
  change Polynomial.aeval ((Ideal.Quotient.mkₐ ℂ I) (X i)) q = 0
  rw [Polynomial.aeval_algHom_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- A polynomial fiber with finitely many complex points has a
finite-dimensional coordinate algebra, even when its ideal is nonradical. -/
theorem finiteDimensional_quotient (I : Ideal (MvPolynomial σ ℂ))
    (hI : (zeroLocus ℂ I).Finite) :
    FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ I) := by
  have hpoly (p : MvPolynomial σ ℂ) : IsIntegral ℂ (Ideal.Quotient.mk I p) := by
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp =>
      simpa only [map_mul] using hp.mul (coordinate_integral I hI i)
  let : Algebra.IsIntegral ℂ (MvPolynomial σ ℂ ⧸ I) := ⟨fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hpoly p⟩
  exact Algebra.IsIntegral.finite

#print axioms coordinate_monic_relation
#print axioms coordinate_integral
#print axioms finiteDimensional_quotient

end FinitenessAllLevelFiniteFiberAlgebra
