module

public import QuantitativeArithmeticTwoSequenceTaylorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor Complex Filter Asymptotics Set MeasureTheory FinitenessFourierConstruction FinitenessPolynomialSeries
open scoped Topology

/-- The all-order Taylor-Mellin relation for two distinct Fourier series;
remainder analyticity and every coefficient integral are derived. -/
theorem two_taylor_mellin_rows {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k a b L r χ M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelAdditive.transform a r s-
          (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
            (∑ n∈Finset.range M, mellinTaylorTerm k b (-1/(L*r)) (L*r^2) r n s)=
          mellin (twoError k a b L r χ M) s := by
  obtain ⟨K,hK⟩ := two_error_analytic hL hr k ha ha0 hb hb0 χ hF
  obtain ⟨C,hC⟩ := frickeTaylorPolynomial_convergent k hb hb0 hL hr
  obtain ⟨D,hD⟩ := frickeTaylorPolynomial_mellin k hb hb0 hL hr
  obtain ⟨E,hE⟩ := additive_convergence_halfplane ha ha0
  let B : ℝ := max (max (K:ℝ) (C:ℝ)) (max D E)
  have hBK : (K:ℝ)≤B := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : (C:ℝ)≤B := (le_max_right _ _).trans (le_max_left _ _)
  have hBD : D≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBE : E≤B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B,?_⟩
  intro M
  constructor
  · intro s hs
    apply hK M s
    change B-(M:ℝ)<s.re at hs
    change (K:ℝ)-(M:ℝ)<s.re
    linarith
  · intro s hs
    have hm := (hasMellin_sub (hE r s (lt_of_le_of_lt hBE hs)).1
      ((hC s (lt_of_le_of_lt hBC hs) M).const_smul (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k)))).2
    rw [mellin_const_smul,hD s (lt_of_le_of_lt hBD hs) M,
      (hE r s (lt_of_le_of_lt hBE hs)).2] at hm
    change mellin (twoError k a b L r χ M) s=_ at hm
    simpa only [smul_eq_mul] using hm.symm


#print axioms two_taylor_mellin_rows
end QuantitativeArithmeticTwoSequenceTaylor
