module

public import FinitenessAllLevelObservableEliminantV1
public import FinitenessAllLevelSeparableEliminantV1
public import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFiniteFiberAlgebra

open MvPolynomial Set

variable {A σ : Type*} [CommRing A]

def rectangleIdeal (q : σ → Polynomial A) : Ideal (MvPolynomial σ A) :=
  Ideal.span (range (fun i => Polynomial.aeval (X i) (q i)))

theorem eval_map_observable (e : A →+* ℂ) (v : σ → ℂ)
    (p : MvPolynomial σ A) (q : Polynomial A) :
    MvPolynomial.aeval v (MvPolynomial.map e (Polynomial.aeval p q)) =
      q.eval₂ e (MvPolynomial.aeval v (MvPolynomial.map e p)) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, Polynomial.eval₂_add, hq, hr]
  | monomial n a => simp [Polynomial.aeval_monomial]

theorem mem_rectangle_zeroLocus (e : A →+* ℂ) (q : σ → Polynomial A) (v : σ → ℂ) :
    v ∈ zeroLocus ℂ ((rectangleIdeal q).map (MvPolynomial.map e)) ↔
      ∀ i, (q i).eval₂ e (v i) = 0 := by
  rw [rectangleIdeal, Ideal.map_span, zeroLocus_span, ← Set.range_comp]
  simp only [mem_ofPred_eq, forall_mem_range, Function.comp_apply, eval_map_observable,
    MvPolynomial.map_X, MvPolynomial.aeval_X]

theorem rectangle_zeroLocus_finite [Finite σ] (e : A →+* ℂ)
    (q : σ → Polynomial A) (hq : ∀ i, (q i).map e ≠ 0) :
    (zeroLocus ℂ ((rectangleIdeal q).map (MvPolynomial.map e))).Finite := by
  apply (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot (hq i))).subset
  intro v hv i
  exact (Polynomial.eval₂_eq_eval_map e).symm.trans ((mem_rectangle_zeroLocus e q v).mp hv i)

/-- An observable on a finite rectangular algebra satisfies an equation
X^n S(X), with S(0) nonzero in the original coefficient domain. This
separates the identically-zero residual from the other residual values. -/
theorem rectangular_residual_certificate [IsDomain A] [Finite σ]
    (e : A →+* ℂ) (he : Function.Injective e)
    (q : σ → Polynomial A) (hq : ∀ i, q i ≠ 0) (p : MvPolynomial σ A) :
    ∃ n : ℕ, ∃ s : Polynomial A, s.coeff 0 ≠ 0 ∧
      Polynomial.aeval p (Polynomial.X ^ n * s) ∈ rectangleIdeal q := by
  have hf := rectangle_zeroLocus_finite e q (fun i h => hq i
    ((Polynomial.map_injective e he) (by simpa only [Polynomial.map_zero] using h)))
  obtain ⟨r, hr, hmem⟩ := observable_eliminant e he (rectangleIdeal q) hf p
  obtain ⟨s, hs, hn⟩ := r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr 0
  simp only [Polynomial.C_0, sub_zero] at hs hn
  exact ⟨r.rootMultiplicity 0, s, fun h => hn (Polynomial.X_dvd_iff.mpr h), hs ▸ hmem⟩

/-- The residual certificate is an exact identity at every specialized
rectangular zero, not merely at the generic parameter. -/
theorem eval_residual_certificate (e : A →+* ℂ) (q : σ → Polynomial A)
    (p : MvPolynomial σ A) (n : ℕ) (s : Polynomial A)
    (hcert : Polynomial.aeval p (Polynomial.X ^ n * s) ∈ rectangleIdeal q)
    (v : σ → ℂ) (hv : ∀ i, (q i).eval₂ e (v i) = 0) :
    (MvPolynomial.aeval v (MvPolynomial.map e p)) ^ n *
      s.eval₂ e (MvPolynomial.aeval v (MvPolynomial.map e p)) = 0 := by
  have h := (mem_rectangle_zeroLocus e q v).mpr hv _
    (Ideal.mem_map_of_mem (MvPolynomial.map e) hcert)
  simpa only [eval_map_observable, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X] using h

#print axioms eval_map_observable
#print axioms mem_rectangle_zeroLocus
#print axioms rectangle_zeroLocus_finite
#print axioms rectangular_residual_certificate
#print axioms eval_residual_certificate

end FinitenessAllLevelFiniteFiberAlgebra
