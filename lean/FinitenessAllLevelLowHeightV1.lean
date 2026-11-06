module

public import FinitenessAllLevelHeightWeightsV1
public import QuantitativeArithmeticRetainedWindowGainV1
public import FinitenessLowHeightV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelLowHeight

open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  QuantitativeArithmeticRetainedWindowGain FinitenessAllLevelHeightWeights
  FinitenessAllLevelGoodTrace FinitenessAnalyticReconstruction
  FinitenessComplexGeometry SpanningIntegerRows

/-- Actual low-height control with both unramified dilation branches. -/
theorem from_FE {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N P Q hQ) (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z) (χ lam : ℕ → ℂ) (m s : ℕ)
    {L : ℝ} (hL : 0 ≤ L) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hlam : ∀ p ∈ P, ‖lam p‖ ≤ L)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ (2 * m) *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (hcomplete : ∀ p ∈ P, ∀ w : ℂ, 0 < w.im →
      completeTwist F p w = firstMultiplier lam m p * F ((p : ℂ) * w) -
        (p : ℂ) ^ (2 * m) * F ((p : ℂ) ^ 2 * w))
    (j : Fin Q) (z : ℂ) {ρ M : ℝ} (hz : 0 < z.im)
    (hρ : 0 < ρ) (hρhalf : 1 / 2 ≤ ρ) (hM : 0 ≤ M) (hs : cost A L * ρ ^ s ≤ 1)
    (hsmall : ∀ i : RowIndex N Q, Sum.inl i ∈ (A.coeff j).support →
      denominator (Nat.lcm N (i.val.1 ^ 2)) (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q) ≤ ρ)
    (habove : ∀ w : ℂ, z.im / ρ ≤ w.im → w.im ^ (m + s) * ‖F w‖ ≤ M) :
    z.im ^ (m + s) * ‖F z‖ ≤ M := by
  let d : AugIndex N (P : Set ℕ) Q → ℝ
    | Sum.inl i => denominator (Nat.lcm N (i.val.1 ^ 2))
        (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q)
    | Sum.inr i => 1 / (i.1.val : ℝ)
  have him (u : ℤ) : (z + ((u : ℂ) - (j : ℕ)) / Q).im = z.im := by simp
  have hLc (i : RowIndex N Q) : (0 : ℝ) < Nat.lcm N (i.val.1 ^ 2) := by
    exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)
  have hd (i : RowIndex N Q) : 0 < d (Sum.inl i) := by
    apply denominator_pos (hLc i)
    simpa only [him] using hz
  apply reconstruct_bound A hL j (twistRow F j z) (F z) m s hz.le hρ.le hM
    (reconstruct_twists A hdiv F hp j z) hs d
  · intro i hi
    cases i with
    | inl x => exact ⟨(hd x).le, hsmall x hi⟩
    | inr x =>
      exact ⟨by dsimp [d]; positivity, prime_reciprocal_le (hP x.1.val x.1.property) hρhalf⟩
  · intro i hi
    cases i with
    | inl x =>
      have hβ : 0 < (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q).im := by
        simpa only [him] using hz
      have hf := FinitenessLowHeight.weighted_twist (M := M) F x.val.1 m s (χ x.val.1)
        (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q) (hLc x) hβ (hχ x.val.1 x.property.1)
        (by simpa using hFE x.val.1 x.property.1 _ hβ) (by
          intro a _
          apply habove
          have ht := translated_reflected_im (hLc x) hβ ((a : ℝ) / x.val.1)
          have ht' : (-1 / (((Nat.lcm N (x.val.1 ^ 2) : ℝ) : ℂ) *
              (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q)) + (a : ℂ) / x.val.1).im =
                z.im / d (Sum.inl x) := by
            simpa [him, d] using ht
          rw [ht']
          exact div_le_div_of_nonneg_left hz.le (hd x) (hsmall x hi))
      simpa only [him, d, twistRow, branchCost] using hf
    | inr x =>
      have hpx := hP x.1.val x.1.property
      have hpR : (1 : ℝ) ≤ x.1.val := by exact_mod_cast hpx.one_lt.le
      have hβ : 0 < (z + ((x.2 : ℂ) - (j : ℕ)) / Q).im := by
        simpa only [him] using hz
      have hheight : z.im / ρ ≤
          ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q)).im := by
        simpa using prime_height_gain hpx hρhalf hz.le
      have hsq (w : ℂ) : ((x.1.val : ℂ) ^ 2 * w).im = (x.1.val : ℝ) ^ 2 * w.im := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have hheight2 : z.im / ρ ≤
          ((x.1.val : ℂ) ^ 2 * (z + ((x.2 : ℂ) - (j : ℕ)) / Q)).im := by
        have hle : (x.1.val : ℝ) ≤ (x.1.val : ℝ) ^ 2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_right hle hz.le
        have hh0 : z.im / ρ ≤ (x.1.val : ℝ) * z.im := by simpa using hheight
        rw [hsq, him]
        exact hh0.trans hh
      have hbound : ((x.1.val : ℝ) * z.im) ^ (m + s) *
          ‖F ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q))‖ ≤ M := by
        simpa using habove _ hheight
      have hbound2 : ((x.1.val : ℝ) ^ 2 * z.im) ^ (m + s) *
          ‖F ((x.1.val : ℂ) ^ 2 * (z + ((x.2 : ℂ) - (j : ℕ)) / Q))‖ ≤ M := by
        simpa only [hsq, him] using habove _ hheight2
      have hf := weighted_two_dilations lam m s hpx hz.le hM hL
        (hlam x.1.val x.1.property) _ _ hbound hbound2
      dsimp only [twistRow, branchCost, d]
      rw [hcomplete x.1.val x.1.property _ hβ]
      exact hf

#print axioms from_FE

end FinitenessAllLevelLowHeight
