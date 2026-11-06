module

public import QuantitativeArithmeticRetainedGlobalHeightV1
public import FinitenessEnvelopeAssemblyV1

@[expose] public section

namespace QuantitativeArithmeticRetainedEnvelope

open QuantitativeArithmeticRetainedGlobalHeight QuantitativeArithmeticRetainedCertificate
  QuantitativeArithmeticRetainedReconstruction FinitenessAnalyticReconstruction
  FinitenessHeightEnvelope FinitenessEnvelopeAssembly

/-- The mixed reconstruction controls growth at height zero from bounded
positive-height tails. The constants are independent of weight and the
admissible retained multipliers. -/
theorem global_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) (P : Parameters A)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (χ b : ℕ → ℂ) (m : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hb : ∀ p ∈ S, ‖b p‖ ≤ (p : ℝ)^m)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^(2*m) *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (hcomplete : ∀ p ∈ S, ∀ z : ℂ, 0 < z.im → completeTwist F p z = b p*F ((p : ℂ)*z))
    (htail : ∀ y : ℝ, 0 < y → ∃ C : ℝ,
      ∀ z : ℂ, y ≤ z.im → z.im^(m+P.s) * ‖F z‖ ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ M = envelope height (value F (m+P.s)) P.ε ∧
      ∀ z : ℂ, 0 < z.im → z.im^(m+P.s) * ‖F z‖ ≤ M := by
  have htailB (y : ℝ) (hy : 0 < y) : BddAbove (tailSet height (value F (m+P.s)) y) := by
    obtain ⟨C,hC⟩ := htail y hy
    refine ⟨C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hC z.val hz
  have hne := tail_nonempty F (m+P.s)
  have hr : 1 < P.ρ⁻¹ := (one_lt_inv₀ P.rho_pos).mpr P.rho_lt_one
  have hpoint (z : Point) (_hz : 0 < height z) (hze : height z < P.ε) :
      value F (m+P.s) z ≤ envelope height (value F (m+P.s)) (P.ρ⁻¹ * height z) := by
    have ht : 0 < P.ρ⁻¹ * height z := mul_pos (inv_pos.mpr P.rho_pos) z.property
    apply pointwise hN A P hprime hdiv F hp χ b m hχ hb hFE hcomplete z.val z.property hze.le
      (envelope_nonneg F (m+P.s) _ ht (htailB _ ht))
    intro w hw
    have hwp : 0 < w.im := (div_pos z.property P.rho_pos).trans_le hw
    exact le_csSup (htailB _ ht)
      ⟨⟨w,hwp⟩, by simpa [height, div_eq_mul_inv, mul_comm] using hw, rfl⟩
  refine ⟨envelope height (value F (m+P.s)) P.ε,
    envelope_nonneg F (m+P.s) P.ε P.epsilon_pos (htailB _ P.epsilon_pos), rfl, ?_⟩
  intro z hz
  exact pointwise_global_bound height (value F (m+P.s)) P.epsilon_pos hr hne htailB hpoint
    ⟨z,hz⟩ hz

#print axioms global_bound

end QuantitativeArithmeticRetainedEnvelope
