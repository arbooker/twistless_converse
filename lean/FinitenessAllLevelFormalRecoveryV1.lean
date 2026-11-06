module

public import FinitenessAllLevelFormalContinuationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelPencilHeights FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight
  FinitenessAllLevelGoodTrace FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem iterate_eq_of_reconstruction (hN : 0 < N) (hp : p.Prime)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (F : space (radius a)) (G : ℂ → ℂ)
    (hinit : ∀ z : ℂ, a ≤ z.im → lift F z = G z)
    (hrec : ∀ z : ℂ, 0 < z.im → z.im < a → step A χ m lam G z = G z)
    (n : ℕ) {z : ℂ} (hz : a * P.ρ ^ n ≤ z.im) :
    iterate A a χ m lam F n z = G z := by
  induction n generalizing z with
  | zero => exact hinit z (by simpa only [pow_zero, mul_one] using hz)
  | succ n ih =>
      by_cases haz : a ≤ z.im
      · rw [iterate_above A a χ m lam F _ haz, hinit z haz]
      · have hpos : 0 < z.im := (mul_pos ha (pow_pos P.rho_pos _)).trans_le hz
        simp only [iterate, ite_eq_right haz]
        rw [step_congr hN hp A P χ m lam (fun w hw => ih hw) hpos
          ((le_of_not_ge haz).trans hae) (by
            apply (le_div_iff₀ P.rho_pos).mpr
            simpa only [pow_succ, mul_assoc] using hz)]
        exact hrec z hpos (lt_of_not_ge haz)

theorem formal_eq_of_reconstruction (hN : 0 < N) (hp : p.Prime)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (F : space (radius a)) (G : ℂ → ℂ)
    (hinit : ∀ z : ℂ, a ≤ z.im → lift F z = G z)
    (hrec : ∀ z : ℂ, 0 < z.im → z.im < a → step A χ m lam G z = G z)
    {z : ℂ} (hz : 0 < z.im) : formal A P a χ m lam F z = G z :=
  iterate_eq_of_reconstruction hN hp A P ha hae χ m lam F G hinit hrec _ (depth_spec A P a hz)

theorem canonical_qParam (z : ℂ) :
    Function.Periodic.qParam 1 (line (coordinate (Function.Periodic.qParam 1 z)) z.im) =
      Function.Periodic.qParam 1 z := by
  apply qParam_coordinate
  simp only [mem_sphere, dist_zero_right, Function.Periodic.norm_qParam, radius, div_one]

/-- Every original Euler solution is recovered globally by the actual
finite reconstruction tree in its derived root-number sector. -/
theorem original_formal (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (m : ℕ) (f : S N (2 * m)) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) ∧
      (∀ q, ‖χ q‖ = 1) ∧ ∀ z : ℂ, 0 < z.im →
        formal A P a χ m (f.val p)
          (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
          fourier (fullCoefficients f.val (2 * m)) z := by
  obtain ⟨χ, hχ, hχnorm, hrec⟩ := original_reconstruction hN A
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using And.intro hp hgood) f.property
  refine ⟨χ, hχ, hχnorm, fun z hz => ?_⟩
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

#print axioms formal_eq_of_reconstruction
#print axioms canonical_qParam
#print axioms original_formal

end FinitenessAllLevelFormalContinuation
