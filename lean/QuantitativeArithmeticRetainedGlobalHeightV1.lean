module

public import QuantitativeArithmeticRetainedLowHeightV1
public import FinitenessGlobalHeightV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedGlobalHeight

open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedHeightWeights
  QuantitativeArithmeticRetainedReconstruction FinitenessAnalyticReconstruction
  FinitenessComplexGeometry SpanningIntegerRows

/-- Fixed strict-height data for the mixed certificate. The exponent and
all constants are independent of the weight and individual solution. -/
structure Parameters {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) where
  ε : ℝ
  ρ : ℝ
  s : ℕ
  epsilon_pos : 0 < ε
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  rho_half : 1 / 2 ≤ ρ
  mass_bound : cost A * ρ ^ s ≤ 1
  small : ∀ j : Fin Q, ∀ i : RowIndex N Q, Sum.inl i ∈ (A.coeff j).support →
    ∀ z : ℂ, (j : ℝ) / Q ≤ z.re → z.re ≤ ((j : ℝ) + 1) / Q →
      0 ≤ z.im → z.im ≤ ε →
      denominator (Nat.lcm N (i.val.1 ^ 2))
        (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q) ≤ ρ

theorem parameters_exist {N Q : ℕ} {P : Finset ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (A : Certificate N P Q hQ) : Nonempty (Parameters A) := by
  obtain ⟨ε, ρ, he, hr, hr1, hrhalf, hb⟩ :=
    QuantitativeArithmeticRetainedWindowGain.certificate_denominator_gain hN hQ A
  obtain ⟨s, hs⟩ := FinitenessIntegerWeight.exists_exponent
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cost A)) hr1
  exact ⟨⟨ε, ρ, s, he, hr, hr1, hrhalf, hs, hb⟩⟩

/-- The actual reconstruction controls a point by values above the fixed
height gain. Periodicity reduces to the certificate's original cells. -/
theorem pointwise {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) (P : Parameters A)
    (hS : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z) (χ b : ℕ → ℂ) (m : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hb : ∀ p ∈ S, ‖b p‖ ≤ (p : ℝ) ^ m)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ (2 * m) *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (hcomplete : ∀ p ∈ S, ∀ w : ℂ, 0 < w.im →
      completeTwist F p w = b p * F ((p : ℂ) * w))
    (z : ℂ) (hz : 0 < z.im) (hze : z.im ≤ P.ε) {M : ℝ} (hM : 0 ≤ M)
    (habove : ∀ w : ℂ, z.im / P.ρ ≤ w.im → w.im ^ (m + P.s) * ‖F w‖ ≤ M) :
    z.im ^ (m + P.s) * ‖F z‖ ≤ M := by
  obtain ⟨w, hw0, hw1, him, hv⟩ := FinitenessGlobalHeight.periodic_reduction F hp z
  obtain ⟨j, hj0, hj1⟩ := FinitenessGlobalHeight.cell_exists hQ hw0 hw1
  have hwp : 0 < w.im := by simpa only [him] using hz
  have hwe : w.im ≤ P.ε := by simpa only [him] using hze
  have h := QuantitativeArithmeticRetainedLowHeight.from_FE hN A hS hdiv F hp χ b m P.s
    hχ hb hFE hcomplete j w hwp P.rho_pos P.rho_half hM P.mass_bound
    (fun i hi => P.small j i hi w hj0 hj1 hwp.le hwe)
    (by simpa only [him] using habove)
  simpa only [him, hv] using h

#print axioms parameters_exist
#print axioms pointwise

end QuantitativeArithmeticRetainedGlobalHeight
