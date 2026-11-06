module

public import QuantitativeArithmeticRetainedEnvelopeV1
public import FinitenessCuspBoundsV1

@[expose] public section

namespace QuantitativeArithmeticRetainedCutoff

open QuantitativeArithmeticRetainedGlobalHeight QuantitativeArithmeticRetainedCertificate
  QuantitativeArithmeticRetainedReconstruction FinitenessAnalyticReconstruction
  FinitenessHeightEnvelope FinitenessEnvelopeAssembly FinitenessDiskDecay Metric

/-- A finite Taylor jet determines a solution of the mixed laws. The
cutoff is linear in the half-weight and uniform in the normalized
ramified dilation coefficients. -/
theorem zero_of_jet {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N S Q hQ) (P : Parameters A)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ Q)
    (F G : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (χ b : ℕ → ℂ) (m : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hb : ∀ p ∈ S, ‖b p‖ ≤ (p : ℝ)^m)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^(2*m) *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (hcomplete : ∀ p ∈ S, ∀ z : ℂ, 0 < z.im → completeTwist F p z = b p*F ((p : ℂ)*z))
    (hG : DifferentiableOn ℂ G (ball 0 1)) (h0 : G 0 = 0)
    (heq : ∀ z : ℂ, 0 < z.im → F z = G (Function.Periodic.qParam 1 z))
    (n : ℕ) (hn : ((m+P.s : ℕ) : ℝ)+1 ≤ Real.pi*(n : ℝ)*P.ε)
    (hzero : ∀ i < n, quotient i G 0 = 0) :
    ∀ z : ℂ, 0 < z.im → F z = 0 := by
  obtain ⟨M,hM0,hMeq,hM⟩ := QuantitativeArithmeticRetainedEnvelope.global_bound
    hN A P hprime hdiv F hp χ b m hχ hb hFE hcomplete
    (fun y hy => FinitenessCuspBounds.tail F G hG h0 heq (m+P.s) hy)
  have hη : 0 < P.ε/2 := half_pos P.epsilon_pos
  have hn' : ((m+P.s : ℕ) : ℝ)+1 ≤ 2*Real.pi*(n : ℝ)*(P.ε/2) := by
    convert hn using 1; ring
  have ht (z : ℂ) (hz : P.ε ≤ z.im) :
      z.im^(m+P.s)*‖F z‖ ≤ Real.exp (-1)*M :=
    FinitenessCuspBounds.weighted_decay F G hG heq (m+P.s) n hzero hη hM0 hM hn'
      (by simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hz)
  have hc : M ≤ Real.exp (-1)*M := by
    rw [hMeq]
    apply csSup_le (tail_nonempty F (m+P.s) P.ε P.epsilon_pos)
    rintro _ ⟨z,hz,rfl⟩
    simpa only [value, ← hMeq] using ht z.val hz
  have hMzero := zero_of_contraction hM0 FinitenessExponentialCutoff.contraction_constant.2 hc
  intro z hz
  have hnorm : ‖F z‖ ≤ 0 := by
    have := hM z hz
    rw [hMzero] at this
    exact nonpos_of_mul_nonpos_right this (pow_pos hz _)
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

#print axioms zero_of_jet

end QuantitativeArithmeticRetainedCutoff
