module

public import QuantitativeArithmeticRetainedHeightWeightsV1
public import QuantitativeArithmeticRetainedWindowGainV1
public import QuantitativeArithmeticRetainedReconstructionV1
public import FinitenessLowHeightV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedLowHeight

open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  QuantitativeArithmeticRetainedHeightWeights QuantitativeArithmeticRetainedWindowGain
  FinitenessAnalyticReconstruction FinitenessComplexGeometry SpanningIntegerRows

/-- The actual mixed low-height estimate: legal primitive rows reflect
upward and retained prime complete rows dilate upward. -/
theorem from_FE {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N P Q hQ) (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z)
    (χ b : ℕ → ℂ) (m s : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hb : ∀ p ∈ P, ‖b p‖ ≤ (p : ℝ) ^ m)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ (2 * m) *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (hcomplete : ∀ p ∈ P, ∀ w : ℂ, 0 < w.im →
      completeTwist F p w = b p * F ((p : ℂ) * w))
    (j : Fin Q) (z : ℂ) {ρ M : ℝ} (hz : 0 < z.im)
    (hρ : 0 < ρ) (hρhalf : 1 / 2 ≤ ρ) (hM : 0 ≤ M) (hs : cost A * ρ ^ s ≤ 1)
    (hsmall : ∀ i : RowIndex N Q, Sum.inl i ∈ (A.coeff j).support →
      denominator (Nat.lcm N (i.val.1 ^ 2)) (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q) ≤ ρ)
    (habove : ∀ w : ℂ, z.im / ρ ≤ w.im → w.im ^ (m + s) * ‖F w‖ ≤ M) :
    z.im ^ (m + s) * ‖F z‖ ≤ M := by
  let d : AugIndex N (P : Set ℕ) Q → ℝ
    | Sum.inl i => denominator (Nat.lcm N (i.val.1 ^ 2))
        (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q)
    | Sum.inr i => 1 / (i.1.val : ℝ)
  have him (u : ℤ) : (z + ((u : ℂ) - (j : ℕ)) / Q).im = z.im := by simp
  have hL (i : RowIndex N Q) : (0 : ℝ) < Nat.lcm N (i.val.1 ^ 2) := by
    exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)
  have hd (i : RowIndex N Q) : 0 < d (Sum.inl i) := by
    apply denominator_pos (hL i)
    simpa only [him] using hz
  apply QuantitativeArithmeticRetainedHeightWeights.reconstruct_bound A j
    (twistRow F j z) (F z) m s hz.le hρ.le hM
    (QuantitativeArithmeticRetainedReconstruction.reconstruct_twists A hdiv F hp j z) hs d
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
        (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q) (hL x) hβ (hχ x.val.1 x.property.1)
        (by simpa using hFE x.val.1 x.property.1 _ hβ) (by
          intro a _
          apply habove
          have ht := translated_reflected_im (hL x) hβ ((a : ℝ) / x.val.1)
          have ht' : (-1 / (((Nat.lcm N (x.val.1 ^ 2) : ℝ) : ℂ) *
              (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q)) + (a : ℂ) / x.val.1).im =
                z.im / d (Sum.inl x) := by
            simpa [him, d] using ht
          rw [ht']
          exact div_le_div_of_nonneg_left hz.le (hd x) (hsmall x hi))
      simpa only [him, d, twistRow, branchCount] using hf
    | inr x =>
      have hpx : (0 : ℝ) < x.1.val := by exact_mod_cast (hP x.1.val x.1.property).pos
      have hβ : 0 < (z + ((x.2 : ℂ) - (j : ℕ)) / Q).im := by
        simpa only [him] using hz
      have hheight : z.im / ρ ≤
          ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q)).im := by
        simpa using prime_height_gain (hP x.1.val x.1.property) hρhalf hz.le
      have hbound : ((x.1.val : ℝ) * z.im) ^ (m + s) *
          ‖F ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q))‖ ≤ M := by
        simpa using habove _ hheight
      have hf := weighted_dilation m s hpx hz.le (hb x.1.val x.1.property) hbound
      dsimp only [twistRow, branchCount, d]
      rw [hcomplete x.1.val x.1.property _ hβ]
      simpa only [Nat.cast_one, one_mul] using hf

#print axioms from_FE

end QuantitativeArithmeticRetainedLowHeight
