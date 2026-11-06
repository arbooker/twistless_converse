module

public import SmallLevelTaylorTermMellinV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Set MeasureTheory FormalMultilinearSeries FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

def mellinTaylorTerm (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (I/(r:ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*(c:ℂ)^(s+(n:ℂ))*
    SmallLevelAdditive.transform a β (s+(n:ℂ))

theorem frickeTaylorPolynomial_sum (k : ℕ) (a : ℕ → ℂ) (L r : ℝ) (M : ℕ) (y : ℝ) :
    frickeTaylorPolynomial k a L r M y=
      ∑ n∈Finset.range M, taylorTerm k a (-1/(L*r)) (L*r^2) r n y := rfl

theorem frickeTaylorPolynomial_convergent (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {L r : ℝ} (hL : 0<L) (hr : r≠0) :
    ∃ K : ℕ, ∀ s : ℂ, (K:ℝ)<s.re → ∀ M : ℕ,
      MellinConvergent (frickeTaylorPolynomial k a L r M) s := by
  obtain ⟨K,hK⟩ := taylorTerm_convergent k ha ha0 (mul_pos hL (sq_pos_of_ne_zero hr))
  refine ⟨K,?_⟩
  intro s hs M
  unfold MellinConvergent
  simp only [frickeTaylorPolynomial_sum,Finset.smul_sum]
  exact integrable_finsetSum (Finset.range M) (fun n _ => hK (-1/(L*r)) r s hs n)

theorem frickeTaylorPolynomial_mellin (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {L r : ℝ} (hL : 0<L) (hr : r≠0) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ M : ℕ,
      mellin (frickeTaylorPolynomial k a L r M) s=
        ∑ n∈Finset.range M, mellinTaylorTerm k a (-1/(L*r)) (L*r^2) r n s := by
  have hc : 0<L*r^2 := mul_pos hL (sq_pos_of_ne_zero hr)
  obtain ⟨K,hK⟩ := taylorTerm_convergent k ha ha0 hc
  obtain ⟨B,hB⟩ := taylorTerm_additive_mellin k ha ha0 hc
  refine ⟨max (K:ℝ) B,?_⟩
  intro s hs M
  have he : mellin (frickeTaylorPolynomial k a L r M) s=
      ∑ n∈Finset.range M, mellin (taylorTerm k a (-1/(L*r)) (L*r^2) r n) s := by
    unfold mellin
    simp only [frickeTaylorPolynomial_sum,Finset.smul_sum]
    exact integral_finsetSum (Finset.range M)
      (fun n _ => hK (-1/(L*r)) r s (lt_of_le_of_lt (le_max_left _ _) hs) n)
  rw [he]
  apply Finset.sum_congr rfl
  intro n _
  exact hB (-1/(L*r)) r s (lt_of_le_of_lt (le_max_right _ _) hs) n

/-- The complete Taylor--Fricke Mellin row, for every order M with one
common initial half-plane. The error is the actual Mellin integral and is
analytic on Re(s)>B-M, with no assumed continuation of additive twists. -/
theorem all_taylor_mellin_rows {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError k a L r χ M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelAdditive.transform a r s-
          (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
            (∑ n∈Finset.range M, mellinTaylorTerm k a (-1/(L*r)) (L*r^2) r n s)=
          mellin (frickeError k a L r χ M) s := by
  obtain ⟨K,hK⟩ := frickeError_mellin_analytic hL hr k ha ha0 χ hF
  obtain ⟨C,hC⟩ := frickeTaylorPolynomial_convergent k ha ha0 hL hr
  obtain ⟨D,hD⟩ := frickeTaylorPolynomial_mellin k ha ha0 hL hr
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
    change mellin (frickeError k a L r χ M) s=_ at hm
    simpa only [smul_eq_mul] using hm.symm

#print axioms frickeTaylorPolynomial_convergent
#print axioms frickeTaylorPolynomial_mellin
#print axioms all_taylor_mellin_rows
end SmallLevelTaylor
