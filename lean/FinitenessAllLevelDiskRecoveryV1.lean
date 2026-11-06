module

public import FinitenessAllLevelEquationSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Function.Periodic FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  FinitenessAllLevelCoefficientFunctional FinitenessAllLevelTaylorGrowth
  FinitenessOriginalInput FinitenessOriginalFourier
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- Agreement with the cusp descent includes the boundary of the initial
disk, because the reconstruction reads its initial data at height a itself. -/
theorem initial_cusp_agree_closed (A : Certificate N {p} Q hQ) {L : ℝ}
    (P : Parameters A L) (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (F : space (radius a)) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) (radius a)) :
    extend F.val w = cuspFunction 1 (formal A P a χ m lam F) w := by
  by_cases hw0 : w = 0
  · subst w
    rw [F.property.2, cuspFunction_zero_of_zero_at_inf (by norm_num)
      (formal_zero_at_inf A P a χ m lam F)]
  · have hi : a ≤ (invQParam 1 w).im := by
      have hnorm : ‖qParam 1 (invQParam 1 w)‖ ≤ radius a := by
        rw [qParam_right_inv (by norm_num) hw0]
        simpa only [mem_closedBall, dist_zero_right] using hw
      rw [norm_qParam, div_one, radius, Real.exp_le_exp] at hnorm
      nlinarith [Real.pi_pos]
    rw [cuspFunction_eq_of_nonzero _ _ hw0, formal_above A P a χ m lam F hi]
    change extend F.val w = extend F.val (qParam 1 (invQParam 1 w))
    rw [qParam_right_inv (by norm_num) hw0]

/-- If the recovered normalized coefficients form an original solution,
its representative is exactly the initial Banach vector, including its
boundary values. This rules out extra disk coordinates in the zero locus. -/
theorem representative_recovered (hN : 0 < N) (hp : p.Prime)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (F : space (radius a))
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F))
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖formal A P a χ m lam F z‖ ≤ M)
    (hf : IsSolution N (2 * m) (fun n => normalizedCLM (radius_pos a) (2 * m) n F)) :
    representative N (2 * m) (radius_pos a) (radius_lt_one ha) ⟨_, hf⟩ = F := by
  obtain ⟨hc, _, _⟩ := coefficients_of_height hN hp A P ha hae χ m lam F he hM hb
  obtain ⟨hG, _, _⟩ := formal_cusp_holomorphic hN hp A P ha hae χ m lam F he
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  change FinitenessAllLevelProperness.diskMap (2 * m) (radius a)
    (fun n => normalizedCLM (radius_pos a) (2 * m) n F) w = F.val w
  unfold FinitenessAllLevelProperness.diskMap
  rw [FinitenessAllLevelTopology.polynomial_diskSeries_apply
    (FinitenessOriginalDiskIndependence.polynomial N (2 * m) ⟨_, hf⟩)
    (radius_pos a).le (radius_lt_one ha) w, full_normalized, hc]
  rw [sum_taylor hG ((closedBall_subset_ball (radius_lt_one ha)) w.property)]
  exact (initial_cusp_agree_closed A P a χ m lam F w.property).symm.trans
    (extend_apply F.val w)

#print axioms initial_cusp_agree_closed
#print axioms representative_recovered

end FinitenessAllLevelFormalContinuation
