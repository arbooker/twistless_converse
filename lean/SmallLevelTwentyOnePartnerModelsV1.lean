module

public import SmallLevelTwentyOneKnownWordsTheoryV4
public import SmallLevelContinuationTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOnePartnerModels
open Complex Set Filter MeasureTheory SmallLevelTaylor SmallLevelAdditive SmallLevelTwentyOne
open FinitenessOriginalFourier FinitenessFourierConstruction

/-- If a Fricke partner belongs to an entire old grid, arbitrarily long
original Taylor expansions give analytic representatives of that additive
twist on arbitrarily far-left half-planes. -/
theorem original_partner_models {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i s, AnalyticAt ℂ (fun z => G z i) s)
    (hGF : ∀ s, BG<s.re → G s=gridVector (2*m) f s)
    (r : ℝ) (hr : r≠0) (t : ℤ) (hpartner : -1/(21*r)=(t:ℝ)/42) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ),
      (∀ (n : ℕ) s, B-(n:ℝ)<s.re → AnalyticAt ℂ (H n) s) ∧
      (∀ (n : ℕ) s, B<s.re → H n s=original (2*m) f r s) := by
  obtain ⟨τ,_hτ,hgrowth⟩ := hf.growth
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*I^(2*m))/(((Real.sqrt 21:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((21:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  obtain ⟨B,hB⟩ := normalized_taylor_mellin_rows (by norm_num : (0:ℝ)<21) hr
    (2*m) (even_two_mul m) (polynomial_bound hf.zero hgrowth (2*m))
    (fullCoefficients_zero hf.zero (2*m)) (ε*I^(2*m)) hF
  let V : ℕ → ℂ → ℂ := fun M s => ∑ n∈Finset.range M,
    (I*(21:ℂ)*(r:ℂ))^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*G (s+n) (gridIndex t)
  let P : ℂ → ℂ := fun s => (ε*I^(2*m))*(((21*r^2:ℝ):ℂ)^(s-((2*m:ℕ):ℂ)/2))
  have hP (s : ℂ) : AnalyticAt ℂ P s := by
    have hn : ((21*r^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
    dsimp [P]
    simp_rw [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  have hV (M : ℕ) (s : ℂ) : AnalyticAt ℂ (V M) s := by
    apply Finset.analyticAt_fun_sum
    intro n _
    exact (analyticAt_const.mul (binomial_shift_analytic (2*m) n s)).mul
      ((hG _ (s+n)).comp (f:=fun z : ℂ => z+n) (analyticAt_id.add analyticAt_const))
  have hVF (M : ℕ) (s : ℂ) (hs : BG<s.re) :
      V M s=normalizedTaylorSum (2*m) (fullCoefficients f (2*m)) 21 r M s := by
    unfold V normalizedTaylorSum
    apply Finset.sum_congr rfl
    intro n _
    have hn : BG<(s+(n:ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hGF _ hn,gridVector_index]
    unfold grid original
    rw [hpartner]
    norm_num
  refine ⟨max B BG,fun M s =>
    mellin (frickeError (2*m) (fullCoefficients f (2*m)) 21 r (ε*I^(2*m)) M) s+P s*V M s,?_,?_⟩
  · intro M s hs
    have hb : B-(M:ℝ)<s.re := by linarith [le_max_left B BG]
    exact ((hB M).1 s hb).add ((hP s).mul (hV M s))
  · intro M s hs
    dsimp only
    rw [hVF M s (lt_of_le_of_lt (le_max_right _ _) hs)]
    have he := (hB M).2 s (lt_of_le_of_lt (le_max_left _ _) hs)
    dsimp [P]
    simpa only [original] using (sub_eq_iff_eq_add.mp he).symm

#print axioms original_partner_models
end SmallLevelTwentyOnePartnerModels
