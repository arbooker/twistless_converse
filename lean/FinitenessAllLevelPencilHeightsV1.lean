module

public import FinitenessAllLevelCertificatePencilV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPencilHeights

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight
  FinitenessComplexGeometry FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedCertificate
  QuantitativeArithmeticRetainedReconstruction QuantitativeArithmeticRetainedWindowGain
  FinitenessAnalyticReconstruction SpanningIntegerRows

theorem lift_representative {N k : ℕ} (f : S N k) {a : ℝ} (ha : 0 < a)
    {z : ℂ} (hz : a ≤ z.im) :
    lift (representative N k (radius_pos a) (radius_lt_one ha) f) z =
      fourier (fullCoefficients f.val k) z := by
  have hq : Function.Periodic.qParam 1 z ∈ closedBall (0 : ℂ) (radius a) := by
    simp only [mem_closedBall, dist_zero_right, Function.Periodic.norm_qParam, div_one, radius]
    apply Real.exp_le_exp.mpr
    have hp := Real.pi_pos
    nlinarith
  rw [FinitenessAllLevelCertificateBoundary.lift, representative, extend, dite_eq_left hq]
  exact FinitenessAllLevelTopology.polynomial_diskSeries_apply
    (FinitenessOriginalDiskIndependence.polynomial N k f) (radius_pos a).le (radius_lt_one ha) _

/-- Every source in a selected certificate row is above the initial disk
height. Hence two functions agreeing there give identical reconstruction rows. -/
theorem rows_agree {N Q p : ℕ} {hQ : 0 < Q} (hN : 0 < N) (hp : p.Prime)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hbe : b ≤ P.ε) (ha : a ≤ b / P.ρ)
    (F G : ℂ → ℂ) (hFG : ∀ z : ℂ, a ≤ z.im → F z = G z)
    (χ c d : ℕ → ℂ) (k : ℕ) (w : ℂ)
    (i : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q)
    (hi : i ∈ (A.coeff (selector Q hQ w)).support) :
    twoDilationRow F k χ c d (selector Q hQ w) (line (coordinate w) b) i =
      twoDilationRow G k χ c d (selector Q hQ w) (line (coordinate w) b) i := by
  let j := selector Q hQ w
  let z := line (coordinate w) b
  have him (u : ℤ) : (z + ((u : ℂ) - (j.val : ℂ)) / Q).im = b := by
    simp [z, line]
  cases i with
  | inl i =>
    have hLc := row_level_pos hN hQ i
    have hβ : 0 < (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q).im := by rw [him]; exact hb
    have hd : 0 < denominator (Nat.lcm N (i.val.1 ^ 2))
        (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q) := denominator_pos hLc hβ
    have hs : denominator (Nat.lcm N (i.val.1 ^ 2))
        (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q) ≤ P.ρ := by
      apply P.small j i hi z
      · simpa only [z, line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] using (selector_bounds Q hQ w).1
      · simpa only [z, line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero] using (selector_bounds Q hQ w).2
      · simpa only [z, line_im] using hb.le
      · simpa only [z, line_im] using hbe
    dsimp only [twoDilationRow, frickeRow]
    congr 1
    unfold twist
    apply Finset.sum_congr rfl
    intro v _
    apply hFG
    have he := translated_reflected_im hLc hβ ((v : ℝ) / i.val.1)
    have he' : (-1 / ((Nat.lcm N (i.val.1 ^ 2) : ℕ) *
        (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)) + (v : ℂ) / i.val.1).im =
        b / denominator (Nat.lcm N (i.val.1 ^ 2))
          (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q) := by simpa [him] using he
    rw [he']
    exact ha.trans (div_le_div_of_nonneg_left hb.le hd hs)
  | inr i =>
    have hpi : i.1.val = p := by simpa using i.1.property
    have hh : a ≤ (i.1.val : ℝ) * b := by
      rw [hpi]
      exact ha.trans (prime_height_gain hp P.rho_half hb.le)
    have hh2 : a ≤ (i.1.val : ℝ) ^ 2 * b := by
      have hp1 : (1 : ℝ) ≤ i.1.val := by rw [hpi]; exact_mod_cast hp.one_lt.le
      have hpp : (i.1.val : ℝ) ≤ (i.1.val : ℝ) ^ 2 := by nlinarith
      exact hh.trans (mul_le_mul_of_nonneg_right hpp hb.le)
    have hfirst : a ≤ ((i.1.val : ℂ) * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q)).im := by
      simpa only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, him] using hh
    have hsecond : a ≤ ((i.1.val : ℂ) ^ 2 * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q)).im := by
      rw [← ofReal_natCast, ← ofReal_pow, mul_im]
      simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
      rw [him]
      exact hh2
    dsimp only [twoDilationRow]
    rw [hFG _ hfirst, hFG _ hsecond]

/-- The heights are chosen from the certificate before the weight, root
numbers, or original solution. -/
theorem heights_exist {N Q p : ℕ} {hQ : 0 < Q}
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L) :
    ∃ a b : ℝ, 0 < b ∧ b < a ∧ b ≤ P.ε ∧ a ≤ b / P.ρ := by
  let b := P.ε / 2
  have hb : 0 < b := half_pos P.epsilon_pos
  have hg : b < b / P.ρ := (lt_div_iff₀ P.rho_pos).mpr (by nlinarith [P.rho_lt_one])
  refine ⟨(b + b / P.ρ) / 2, b, hb, by linarith, ?_, by linarith⟩
  dsimp [b]
  linarith [P.epsilon_pos]

#print axioms lift_representative
#print axioms rows_agree
#print axioms heights_exist

end FinitenessAllLevelPencilHeights
