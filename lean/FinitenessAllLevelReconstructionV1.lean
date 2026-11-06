module

public import FinitenessAllLevelGoodTraceV1
public import FinitenessAllLevelAuxiliaryV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelReconstruction

open Complex FinitenessFourierConstruction FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessAnalyticReconstruction QuantitativeArithmeticRetainedCertificate
  QuantitativeArithmeticRetainedReconstruction FinitenessAllLevelGoodTrace

variable {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}

/-- The retained row contains both upward dilations at a good prime. -/
noncomputable def twoDilationRow (F : ℂ → ℂ) (k : ℕ) (χ b d : ℕ → ℂ)
    (j : Fin Q) (z : ℂ) : SpanningIntegerRows.AugIndex N (P : Set ℕ) Q → ℂ
  | Sum.inl x => frickeRow (P := P) F k χ j z (Sum.inl x)
  | Sum.inr x =>
    b x.1.val * F ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q)) -
    d x.1.val * F ((x.1.val : ℂ) ^ 2 * (z + ((x.2 : ℂ) - (j : ℕ)) / Q))

theorem reconstruct_FE_two_dilations (A : Certificate N P Q hQ)
    (hdiv : ∀ p ∈ P, p ∣ Q) (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z)
    (k : ℕ) (χ b d : ℕ → ℂ)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ k *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (hcomplete : ∀ p ∈ P, ∀ w : ℂ, 0 < w.im →
      completeTwist F p w = b p * F ((p : ℂ) * w) - d p * F ((p : ℂ) ^ 2 * w))
    (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :
    F z = ∑ i ∈ (A.coeff j).support,
      (A.coeff j i : ℂ) * twoDilationRow F k χ b d j z i := by
  rw [reconstruct_FE A hdiv F hp k χ hFE j z hz]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl x => rfl
  | inr x =>
    dsimp only [frickeRow, twoDilationRow]
    rw [hcomplete x.1.val x.1.property]
    simpa using hz

/-- Actual original solutions obey the two-dilation reconstruction identity.
The functional equations and the Hecke rows are both derived, not assumed. -/
theorem original_reconstruction (hN : 0 < N) (A : Certificate N P Q hQ)
    (hdiv : ∀ p ∈ P, p ∣ Q) (hprimes : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ N)
    {m : ℕ} {f : ℕ → ℂ} (hf : IsSolution N (2 * m) f) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
      (∀ q, ‖χ q‖ = 1) ∧ ∀ j : Fin Q, ∀ z : ℂ, 0 < z.im →
      fourier (fullCoefficients f (2 * m)) z =
        ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
          twoDilationRow (fourier (fullCoefficients f (2 * m))) (2 * m) χ
            (firstMultiplier f m) (fun p => (p : ℂ) ^ (2 * m)) j z i := by
  obtain ⟨χ, hχ, hχnorm, hFE⟩ :=
    FinitenessOriginalTwistedContinuations.solution_laws hN hQ hf
  refine ⟨χ, hχ, hχnorm, fun j z hz => ?_⟩
  apply reconstruct_FE_two_dilations A hdiv _ (periodic _) (2 * m) χ _ _ hFE _ j z hz
  intro p hp w hw
  exact original_complete_even hf.toEulerData (hprimes p hp).1 (hprimes p hp).2 m hw

/-- For every level and every large good prime there is an actual finite
rational reconstruction certificate, valid for every original solution. -/
theorem exists_original_reconstruction {p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, ∃ A : Certificate N {p} Q hQ,
      N ∣ Q ∧ p ∣ Q ∧ ∀ m : ℕ, ∀ f : ℕ → ℂ, IsSolution N (2 * m) f →
      ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
        (∀ q, ‖χ q‖ = 1) ∧ ∀ j : Fin Q, ∀ z : ℂ, 0 < z.im →
        fourier (fullCoefficients f (2 * m)) z =
          ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
            twoDilationRow (fourier (fullCoefficients f (2 * m))) (2 * m) χ
              (firstMultiplier f m) (fun q => (q : ℂ) ^ (2 * m)) j z i := by
  obtain ⟨Q, hQ, hNQ, hpQ, ⟨A⟩⟩ :=
    FinitenessAllLevelAuxiliary.certificate_at_prime hN hp hlarge
  refine ⟨Q, hQ, A, hNQ, hpQ, fun m f hf => ?_⟩
  apply original_reconstruction hN A _ _ hf
  · intro q hq
    simpa only [Finset.mem_singleton.mp hq] using hpQ
  · intro q hq
    simpa only [Finset.mem_singleton.mp hq] using And.intro hp hgood

#print axioms reconstruct_FE_two_dilations
#print axioms original_reconstruction
#print axioms exists_original_reconstruction

end FinitenessAllLevelReconstruction
