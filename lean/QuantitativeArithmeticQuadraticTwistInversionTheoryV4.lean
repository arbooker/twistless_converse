module

public import FinitenessAllLevelMellinNormalizationV1
public import FinitenessInputBoundsV1
public import FinitenessOriginalFrickeV1
public import Mathlib.NumberTheory.LSeries.Linearity
public import QuantitativeArithmeticMellinScaleV1

/-! Consolidated chapter: QuantitativeArithmeticQuadraticTwistInversion. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticQuadraticTwistInversionScaledV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistInversion

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay
  FinitenessAllLevelMellinNormalization FinitenessInputBounds

/-- A one-sequence Mellin converse. No Euler factors, multiplicativity, or
Ramanujan-twist equations are required. The continued Mellin transform must
be entire of finite order; entireness alone is not substituted for this bound. -/
theorem scaled_mellin_fricke {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) {τ : ℝ} (hg : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (H : ℂ → ℂ) (hhol : Differentiable ℂ H) (hfinite : FiniteOrder H)
    {B : ℝ} (hinit : ∀ s : ℂ, B < s.re →
      H s = mellin (axis N (fullCoefficients f k)) s)
    {ε : ℂ} (hε : ‖ε‖ = 1) (hFE : ∀ s : ℂ, H s = ε * H ((k : ℂ) - s)) :
    ∀ z : ℂ, 0 < z.im → fourier (fullCoefficients f k) z =
      (ε * I^k) / (((Real.sqrt N : ℂ) * z)^k) *
        fourier (fullCoefficients f k) (-1 / ((N : ℂ) * z)) := by
  let α : ℂ := ((k : ℂ) - 1) / 2
  let F : ℂ → ℂ := fun s => constant N k * H (s + α)
  have hFhol : Differentiable ℂ F :=
    (hhol.comp (differentiable_id.add_const α)).const_mul (constant N k)
  have hFfinite : FiniteOrder F := bound_finiteOrder
    (FinitenessFiniteOrder.mul (bound_const (constant N k))
      (bound_shift (finiteOrder_bound hhol.continuous hfinite) α))
  obtain ⟨c, hc⟩ := completion_eq hN hf0 hg
  have hFinit : ∀ s : ℂ, max c (B - α.re) < s.re → F s = completed N k f s := by
    intro s hs
    have hsB : B < (s + α).re := by
      rw [add_re]
      linarith [lt_of_le_of_lt (le_max_right c (B - α.re)) hs]
    change constant N k * H (s + α) = _
    rw [hinit (s + α) hsB]
    exact hc s (lt_of_le_of_lt (le_max_left c (B - α.re)) hs)
  have hFFE : ∀ s : ℂ, F s = ε * F (1 - s) := by
    intro s
    dsimp [F]
    rw [hFE (s + α), show (k : ℂ) - (s + α) = (1 - s) + α by dsimp [α]; ring]
    ring
  exact FinitenessOriginalFricke.fricke_with_sign hN hf0 hg F hFhol hFfinite hFinit hε hFFE

#print axioms scaled_mellin_fricke

end QuantitativeArithmeticQuadraticTwistInversion
end
end

/-! ## QuantitativeArithmeticQuadraticTwistInversionUnscaledV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistInversion

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay
  FinitenessAllLevelMellinNormalization FinitenessInputBounds

/-- Classical unscaled Mellin normalization. This bridge uses the actual
Mellin transform on an initial half-plane and has no twisted Euler-data premise. -/
theorem unscaled_mellin_fricke {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) {τ : ℝ} (hg : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (G : ℂ → ℂ) (hhol : Differentiable ℂ G) (hfinite : FiniteOrder G)
    {B : ℝ} (hinit : ∀ s : ℂ, B < s.re →
      G s = mellin (axis 1 (fullCoefficients f k)) s)
    {ε : ℂ} (hε : ‖ε‖ = 1)
    (hFE : ∀ s : ℂ, G s = ε * (N : ℂ)^((k : ℂ)/2-s) * G ((k : ℂ)-s)) :
    ∀ z : ℂ, 0 < z.im → fourier (fullCoefficients f k) z =
      (ε * I^k) / (((Real.sqrt N : ℂ) * z)^k) *
        fourier (fullCoefficients f k) (-1 / ((N : ℂ) * z)) := by
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsne : (Real.sqrt N : ℂ) ≠ 0 := ofReal_ne_zero.mpr hspos.ne'
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let H : ℂ → ℂ := fun s => (Real.sqrt N : ℂ)^s * G s
  have hp : (fun s : ℂ => (Real.sqrt N : ℂ)^s) =
      fun s : ℂ => exp ((Real.log (Real.sqrt N) : ℂ) * s) := by
    funext s
    rw [cpow_def_of_ne_zero hsne, ← ofReal_log hspos.le]
  have hHhol : Differentiable ℂ H := by
    apply Differentiable.mul _ hhol
    change Differentiable ℂ (fun s : ℂ => (Real.sqrt N : ℂ)^s)
    rw [hp]
    fun_prop
  have hHfinite : FiniteOrder H := by
    apply bound_finiteOrder
    apply FinitenessFiniteOrder.mul _ (finiteOrder_bound hhol.continuous hfinite)
    change FinitenessFiniteOrder.Bound (fun s : ℂ => (Real.sqrt N : ℂ)^s)
    rw [hp]
    exact FinitenessFiniteOrder.exp_linear _
  have hHinit : ∀ s : ℂ, B < s.re → H s = mellin (axis N (fullCoefficients f k)) s := by
    intro s hs
    dsimp [H]
    rw [hinit s hs, QuantitativeArithmeticMellinScale.mellin_one_scale hN,
      ← mul_assoc, ← cpow_add _ _ hsne, add_neg_cancel, cpow_zero, one_mul]
  have hHFE : ∀ s : ℂ, H s = ε * H ((k : ℂ)-s) := by
    intro s
    dsimp [H]
    rw [hFE s, sqrt_cpow hN, sqrt_cpow hN]
    calc
      _ = ε * ((N : ℂ)^(s/2) * (N : ℂ)^((k : ℂ)/2-s)) * G ((k : ℂ)-s) := by ring
      _ = _ := by
        rw [← cpow_add _ _ hNne, show s/2+((k : ℂ)/2-s)=((k : ℂ)-s)/2 by ring]
        ring
  exact scaled_mellin_fricke hN hf0 hg H hHhol hHfinite hHinit hε hHFE

#print axioms unscaled_mellin_fricke

end QuantitativeArithmeticQuadraticTwistInversion
end
end

/-! ## QuantitativeArithmeticQuadraticTwistInversionCombinationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistInversion

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay SmallLevelAdditive
  FinitenessAllLevelMellinDirichlet FinitenessPolynomialSeries

def fourCoefficients (a : ℕ → ℂ) (r₁ r₂ r₃ r₄ : ℝ) (n : ℕ) : ℂ :=
  coefficients a r₁ n + coefficients a r₂ n - coefficients a r₃ n - coefficients a r₄ n

theorem four_zero {a : ℕ → ℂ} (ha : a 0 = 0) (r₁ r₂ r₃ r₄ : ℝ) :
    fourCoefficients a r₁ r₂ r₃ r₄ 0 = 0 := by
  simp [fourCoefficients, coefficients, ha]

theorem four_growth {a : ℕ → ℂ} {τ : ℝ}
    (ha : a =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (r₁ r₂ r₃ r₄ : ℝ) :
    fourCoefficients a r₁ r₂ r₃ r₄ =O[atTop] (fun n : ℕ => (n : ℝ)^τ) :=
  (((coefficients_growth ha r₁).add (coefficients_growth ha r₂)).sub
    (coefficients_growth ha r₃)).sub (coefficients_growth ha r₄)

theorem four_full (f : ℕ → ℂ) (k : ℕ) (r₁ r₂ r₃ r₄ : ℝ) :
    fullCoefficients (fourCoefficients f r₁ r₂ r₃ r₄) k =
      fourCoefficients (fullCoefficients f k) r₁ r₂ r₃ r₄ := by
  funext n
  simp only [fullCoefficients, FinitenessGrowthNormalization.normalized,
    fourCoefficients, coefficients]
  ring

theorem four_fourier {a : ℕ → ℂ} (ha : PolynomialBound a)
    (r₁ r₂ r₃ r₄ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    fourier (fourCoefficients a r₁ r₂ r₃ r₄) z =
      fourier a (z+r₁) + fourier a (z+r₂) - fourier a (z+r₃) - fourier a (z+r₄) := by
  rw [← fourier_translate a r₁, ← fourier_translate a r₂,
    ← fourier_translate a r₃, ← fourier_translate a r₄]
  simp only [fourier_eq_exp]
  simp only [fourCoefficients, add_mul, sub_mul]
  have h₁ := exp_summable (coefficients_polynomial ha r₁) hz
  have h₂ := exp_summable (coefficients_polynomial ha r₂) hz
  have h₃ := exp_summable (coefficients_polynomial ha r₃) hz
  have h₄ := exp_summable (coefficients_polynomial ha r₄) hz
  rw [((h₁.add h₂).sub h₃).tsum_sub h₄, (h₁.add h₂).tsum_sub h₃, h₁.tsum_add h₂]


/-- Initial Mellin agreement for the actual signed additive twist. -/
theorem four_initial {k : ℕ} {f : ℕ → ℂ} (hf0 : f 0 = 0) {τ : ℝ}
    (hg : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (r₁ r₂ r₃ r₄ : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, B < s.re →
      mellin (axis 1 (fullCoefficients (fourCoefficients f r₁ r₂ r₃ r₄) k)) s =
        original k f r₁ s + original k f r₂ s - original k f r₃ s - original k f r₄ s := by
  let a := fullCoefficients f k
  have ha := polynomial_bound hf0 hg k
  have ha0 := fullCoefficients_zero hf0 k
  obtain ⟨d, hd⟩ := polynomial_growth ha
  have hfourpol := polynomial_bound (four_zero hf0 r₁ r₂ r₃ r₄)
    (four_growth hg r₁ r₂ r₃ r₄) k
  rw [four_full] at hfourpol
  refine ⟨(d : ℝ)+1, ?_⟩
  intro s hs
  rw [four_full]
  have hm := mellin_eq_transform hfourpol (four_zero ha0 r₁ r₂ r₃ r₄)
    (four_growth hd r₁ r₂ r₃ r₄) 0 hs
  have hz : (fun t : ℝ => fourier (fourCoefficients a r₁ r₂ r₃ r₄)
      ((0 : ℂ) + (t : ℂ)*I)) = axis 1 (fourCoefficients a r₁ r₂ r₃ r₄) := by
    funext t
    simp [axis]
  simp only [ofReal_zero] at hm
  rw [hz] at hm
  rw [hm]
  have hc : coefficients (fourCoefficients a r₁ r₂ r₃ r₄) 0 =
      (coefficients a r₁ + coefficients a r₂ - coefficients a r₃ - coefficients a r₄) := by
    funext n
    simp [coefficients, phase, fourCoefficients]
  simp only [original, transform]
  change Gamma s * ((2*Real.pi : ℝ) : ℂ)^(-s) *
      LSeries (coefficients (fourCoefficients a r₁ r₂ r₃ r₄) 0) s = _
  rw [hc, LSeries_sub ((summable_at hd r₁ hs).add (summable_at hd r₂ hs) |>.sub
    (summable_at hd r₃ hs)) (summable_at hd r₄ hs),
    LSeries_sub ((summable_at hd r₁ hs).add (summable_at hd r₂ hs)) (summable_at hd r₃ hs),
    LSeries_add (summable_at hd r₁ hs) (summable_at hd r₂ hs)]
  ring

#print axioms four_fourier
#print axioms four_initial

end QuantitativeArithmeticQuadraticTwistInversion
end
end

/-! ## QuantitativeArithmeticQuadraticTwistInversionFourV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistInversion

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction SmallLevelAdditive

/-- The Fourier inversion required for a quadratic twist expressed by four
additive translates. Only the original coefficient growth is needed. The
analytic input is genuine entire finite-order continuation and its FE. -/
theorem four_translate_fricke {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) {τ : ℝ} (hg : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (r₁ r₂ r₃ r₄ : ℝ) (G : ℂ → ℂ)
    (hhol : Differentiable ℂ G) (hfinite : FiniteOrder G)
    {B : ℝ} (hinit : ∀ s : ℂ, B < s.re → G s =
      original k f r₁ s + original k f r₂ s - original k f r₃ s - original k f r₄ s)
    {ε : ℂ} (hε : ‖ε‖ = 1)
    (hFE : ∀ s : ℂ, G s = ε * (N : ℂ)^((k : ℂ)/2-s) * G ((k : ℂ)-s)) :
    let F : ℂ → ℂ := fun z =>
      fourier (fullCoefficients f k) (z+r₁) + fourier (fullCoefficients f k) (z+r₂) -
      fourier (fullCoefficients f k) (z+r₃) - fourier (fullCoefficients f k) (z+r₄)
    ∀ z : ℂ, 0 < z.im → F z =
      (ε * I^k) / (((Real.sqrt N : ℂ) * z)^k) * F (-1 / ((N : ℂ) * z)) := by
  obtain ⟨C,hC⟩ := four_initial hf0 hg r₁ r₂ r₃ r₄ (k := k)
  have hinit' : ∀ s : ℂ, max B C < s.re → G s =
      mellin (FinitenessAllLevelAxisDecay.axis 1
        (fullCoefficients (fourCoefficients f r₁ r₂ r₃ r₄) k)) s := by
    intro s hs
    rw [hinit s (lt_of_le_of_lt (le_max_left B C) hs),
      hC s (lt_of_le_of_lt (le_max_right B C) hs)]
  have he := unscaled_mellin_fricke hN (four_zero hf0 r₁ r₂ r₃ r₄)
    (four_growth hg r₁ r₂ r₃ r₄) G hhol hfinite hinit' hε hFE
  have ha := polynomial_bound hf0 hg k
  dsimp
  intro z hz
  have hNz : 0 < ((N : ℂ)*z).im := by
    simpa only [mul_im, natCast_re, natCast_im, zero_mul, add_zero] using
      mul_pos (show (0 : ℝ) < N by exact_mod_cast hN) hz
  have hNz0 : (N : ℂ)*z ≠ 0 := by
    intro hh
    simp [hh] at hNz
  have hz' : 0 < (-1 / ((N : ℂ)*z)).im := by
    simp only [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hNz (normSq_pos.mpr hNz0)
  have hh := he z hz
  rw [four_full, four_fourier ha r₁ r₂ r₃ r₄ hz,
    four_fourier ha r₁ r₂ r₃ r₄ hz'] at hh
  exact hh

#print axioms four_translate_fricke

end QuantitativeArithmeticQuadraticTwistInversion
end
end
