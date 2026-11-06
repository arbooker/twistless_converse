module

public import FinitenessAllLevelSharpDegreeV1
public import FinitenessAllLevelPolynomialBoundV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelEigenvalueDegree
  QuantitativeArithmeticRetainedCertificate

/-- The actual sharp height estimate, with the constant chosen before the
unbounded eigenvalue, the initial function and the spatial point. -/
theorem formal_sharp_height {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ) (F : space (radius a)) (z : ℂ),
      a / (p : ℝ) ^ j ≤ z.im →
        ‖formal A P a χ m lam F z‖ ≤ C * (1 + ‖lam‖) ^ j * ‖F‖ := by
  have hy : 0 < a / (p : ℝ) ^ j := div_pos ha (pow_pos (Nat.cast_pos.mpr hp.pos) _)
  obtain ⟨B, hB, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m (by norm_num : (0 : ℝ) ≤ 1) hy
  refine ⟨(j + 1 : ℝ) * B, by positivity, fun lam F z hz => ?_⟩
  have h := (formal_sharp_degree hN hp A P ha hae χ m F j hz).global_bound
    (mul_nonneg hB (norm_nonneg F)) (fun w hw => hb w
      (by simpa only [mem_sphere, dist_zero_right] using hw.le) F z hz) lam
  convert h using 1
  ring

#print axioms formal_sharp_height

end FinitenessAllLevelFormalContinuation
