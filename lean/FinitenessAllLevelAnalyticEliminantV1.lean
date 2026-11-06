module

public import FinitenessAllLevelCoefficientRingV1
public import FinitenessAllLevelAlgebraicEliminantV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open Complex Set MvPolynomial Filter
open scoped Topology

variable {ι σ : Type*}
  {U : Set ℂ} (g : ι → ℂ → ℂ)

/-- The zero relation in the coefficient ring is an identity on the entire
domain, so a nonzero element has a nonzero analytic representative. -/
theorem representative_not_identically_zero (a : ring U g) (ha : a ≠ 0) :
    ¬ EqOn (representative U g a) 0 U := by
  intro h
  apply ha
  apply Subtype.ext
  funext z
  exact (representative_agrees U g a z).symm.trans (h z.property)

/-- A polynomial in the original ideal vanishes after every coefficient
specialization at every common zero of the specialized ideal. -/
theorem eval_eliminant (I : Ideal (MvPolynomial σ (ring U g)))
    (q : Polynomial (ring U g)) (i : σ) (hq : Polynomial.aeval (X i) q ∈ I)
    (z : U) (v : σ → ℂ)
    (hv : v ∈ zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z)))) :
    q.eval₂ (evaluation U g z) (v i) = 0 := by
  let e := evaluation U g z
  have he : MvPolynomial.aeval v (MvPolynomial.map e (Polynomial.aeval (X i) q)) = 0 :=
    hv _ (Ideal.mem_map_of_mem (MvPolynomial.map e) hq)
  have hpoly (p : Polynomial (ring U g)) :
      MvPolynomial.aeval v (MvPolynomial.map e (Polynomial.aeval (X i) p)) =
        p.eval₂ e (v i) := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [map_add, Polynomial.eval₂_add, hp, hr]
    | monomial n a =>
      simp [Polynomial.aeval_monomial, e]
  exact (hpoly q).symm.trans he

/-- A single generic finite fiber produces a polynomial eliminant valid on
the WHOLE connected chart domain. All its coefficients are holomorphic, and
its leading coefficient is not identically zero. This upgrades the earlier
fiberwise relations to a genuine analytic-family relation. -/
theorem analytic_coordinate_eliminant [Countable ι] [Finite σ]
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (I : Ideal (MvPolynomial σ (ring U g)))
    (hf : ∀ z : U, (zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z)))).Finite)
    (i : σ) :
    ∃ q : Polynomial (ring U g), q ≠ 0 ∧
      (∀ j, AnalyticOnNhd ℂ (representative U g (q.coeff j)) U) ∧
      (¬ EqOn (representative U g q.leadingCoeff) 0 U) ∧
      ∀ z : U, ∀ v ∈ zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z))),
        q.eval₂ (evaluation U g z) (v i) = 0 := by
  obtain ⟨w, _, hw⟩ := exists_injective_evaluation U g hconn hg hU (Subset.refl U) hne
  let := Function.Injective.isDomain (evaluation U g w) hw
  obtain ⟨q, hq, hmem⟩ := FinitenessAllLevelFiniteFiberAlgebra.coordinate_eliminant
    (evaluation U g w) hw I (hf w) i
  exact ⟨q, hq, fun j => representative_analytic U g hg _,
    representative_not_identically_zero g q.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hq),
    fun z v hv => eval_eliminant g I q i hmem z v hv⟩

/-- The leading coefficient of an analytic-family eliminant is nonzero in
a punctured neighborhood of every point of the connected chart domain. -/
theorem leading_nonzero_punctured (hconn : IsPreconnected U)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    {q : Polynomial (ring U g)} (hq : q ≠ 0) {w : ℂ} (hw : w ∈ U) :
    ∀ᶠ z in 𝓝[≠] w, representative U g q.leadingCoeff z ≠ 0 := by
  have ha := representative_analytic U g hg q.leadingCoeff
  rcases (ha w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact False.elim ((representative_not_identically_zero g q.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hq))
      (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw hz))
  · exact hz

#print axioms representative_not_identically_zero
#print axioms eval_eliminant
#print axioms analytic_coordinate_eliminant
#print axioms leading_nonzero_punctured

end FinitenessAllLevelCoefficientRing
