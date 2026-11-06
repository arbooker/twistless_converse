module

public import FinitenessAllLevelDiskRecoveryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelPencilHeights FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight
  FinitenessAllLevelGoodTrace FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- Every original Euler solution is recovered globally by the actual
finite reconstruction tree in its derived root-number sector. -/
theorem original_formal_with_laws (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (m : ℕ) (f : S N (2 * m)) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
      (∀ q, ‖χ q‖ = 1) ∧
      FinitenessHolomorphicSpace.Laws N Q χ m (fourier (fullCoefficients f.val (2 * m))) ∧
      ∀ z : ℂ, 0 < z.im →
        formal A P a χ m (f.val p)
          (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
          fourier (fullCoefficients f.val (2 * m)) z := by
  obtain ⟨χ, hχ, hχnorm, hFE⟩ :=
    FinitenessOriginalTwistedContinuations.solution_laws hN hQ f.property
  have hrec (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :=
    reconstruct_FE_two_dilations A
      (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
      (fourier (fullCoefficients f.val (2 * m))) (periodic _) (2 * m) χ
      (firstMultiplier f.val m) (fun q => (q : ℂ) ^ (2 * m)) hFE
      (by
        intro q hq w hw
        have heq : q = p := Finset.mem_singleton.mp hq
        subst q
        exact original_complete_even f.property.toEulerData hp hgood m hw) j z hz
  refine ⟨χ, hχ, hχnorm, hFE, fun z hz => ?_⟩
  apply formal_eq_of_reconstruction hN hp A P ha hae χ m (f.val p) _
    (fourier (fullCoefficients f.val (2 * m))) (fun w hw => lift_representative f ha hw) _ hz
  intro w hw _
  have hh := hrec (selector Q hQ (Function.Periodic.qParam 1 w))
    (line (coordinate (Function.Periodic.qParam 1 w)) w.im) (by simpa only [line_im] using hw)
  unfold step
  calc
    _ = ∑ i ∈ (A.coeff (selector Q hQ (Function.Periodic.qParam 1 w))).support,
        (A.coeff (selector Q hQ (Function.Periodic.qParam 1 w)) i : ℂ) *
          twoDilationRow (fourier (fullCoefficients f.val (2 * m))) (2 * m) χ
            (firstMultiplier f.val m) (fun q => (q : ℂ) ^ (2 * m))
            (selector Q hQ (Function.Periodic.qParam 1 w))
            (line (coordinate (Function.Periodic.qParam 1 w)) w.im) i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      cases i with
      | inl i => rfl
      | inr i =>
          have hpi : i.1.val = p := by simpa using i.1.property
          simp only [twoDilationRow, firstMultiplier, hpi]
    _ = fourier (fullCoefficients f.val (2 * m))
        (line (coordinate (Function.Periodic.qParam 1 w)) w.im) := hh.symm
    _ = fourier (fullCoefficients f.val (2 * m)) w := by
      unfold fourier
      rw [canonical_qParam]

#print axioms original_formal_with_laws

end FinitenessAllLevelFormalContinuation
