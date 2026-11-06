module

public import FinitenessAllLevelAnalyticEliminantV1
public import FinitenessAllLevelSeparableEliminantV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientRing

open Complex Set MvPolynomial

variable {ι σ : Type*} {U : Set ℂ} (g : ι → ℂ → ℂ)

theorem eval_radical_eliminant (I : Ideal (MvPolynomial σ (ring U g)))
    (q : Polynomial (ring U g)) (i : σ) (hq : Polynomial.aeval (X i) q ∈ I.radical)
    (z : U) (v : σ → ℂ)
    (hv : v ∈ zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z)))) :
    q.eval₂ (evaluation U g z) (v i) = 0 := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hq
  have he := eval_eliminant g I (q ^ n) i (by simpa only [map_pow] using hn) z v hv
  rw [Polynomial.eval₂_pow] at he
  exact eq_zero_of_pow_eq_zero he

/-- All coordinates have analytic-family eliminating polynomials whose
roots are simple at ONE common generic parameter. The relations hold on
the whole chart, including the exceptional parameters. -/
theorem generic_separable_eliminants [Countable ι] [Finite σ]
    (hU : IsPreconnected U) (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (I : Ideal (MvPolynomial σ (ring U g)))
    (hf : ∀ z : U, (zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z)))).Finite)
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) (hne : V.Nonempty) :
    ∃ w : U, w.val ∈ V ∧ ∀ i : σ,
      ∃ q : Polynomial (ring U g), q ≠ 0 ∧ (q.map (evaluation U g w)).Separable ∧
        (∀ j, AnalyticOnNhd ℂ (representative U g (q.coeff j)) U) ∧
        ∀ z : U, ∀ v ∈ zeroLocus ℂ (I.map (MvPolynomial.map (evaluation U g z))),
          q.eval₂ (evaluation U g z) (v i) = 0 := by
  obtain ⟨w, hwV, hw⟩ := exists_injective_evaluation U g hU hg hV hVU hne
  let := Function.Injective.isDomain (evaluation U g w) hw
  let : CharZero (ring U g) := ⟨fun a b h => by
    have he := congrArg (evaluation U g w) h
    simpa only [map_natCast, Nat.cast_inj] using he⟩
  refine ⟨w, hwV, fun i => ?_⟩
  obtain ⟨q, hq, hs, hi⟩ := FinitenessAllLevelFiniteFiberAlgebra.separable_coordinate_eliminant
    (evaluation U g w) hw I (hf w) i
  exact ⟨q, hq, hs, fun j => representative_analytic U g hg _,
    fun z v hv => eval_radical_eliminant g I q i hi z v hv⟩

#print axioms eval_radical_eliminant
#print axioms generic_separable_eliminants

end FinitenessAllLevelCoefficientRing
