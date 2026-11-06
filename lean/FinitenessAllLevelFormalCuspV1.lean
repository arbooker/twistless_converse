module

public import FinitenessAllLevelCauchyChartV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Filter FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelGlobalHeight QuantitativeArithmeticRetainedCertificate
  Function.Periodic
open scoped Topology

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem step_periodic (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) (G : ℂ → ℂ) : Function.Periodic (step A χ m lam G) 1 := by
  intro z
  simp only [step, FinitenessFourierConstruction.q_periodic z, add_im, one_im, add_zero]

theorem iterate_periodic (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ)
    (m : ℕ) (lam : ℂ) (F : space (radius a)) (n : ℕ) :
    Function.Periodic (iterate A a χ m lam F n) 1 := by
  intro z
  cases n with
  | zero =>
    simp only [iterate, FinitenessAllLevelCertificateBoundary.lift,
      FinitenessFourierConstruction.q_periodic z]
  | succ n =>
    simp only [iterate, add_im, one_im, add_zero,
      FinitenessAllLevelCertificateBoundary.lift, FinitenessFourierConstruction.q_periodic z,
      step_periodic A χ m lam (iterate A a χ m lam F n) z]

theorem formal_periodic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    Function.Periodic (formal A P a χ m lam F) 1 := by
  intro z
  have hd : depth A P a (z + 1) = depth A P a z := by
    simp only [depth, add_im, one_im, add_zero]
  simp only [formal, hd, iterate_periodic A a χ m lam F (depth A P a z) z]

theorem formal_above (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    {z : ℂ} (hz : a ≤ z.im) : formal A P a χ m lam F z = lift F z :=
  iterate_above A a χ m lam F _ hz

theorem formal_zero_at_inf (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    ZeroAtFilter (comap Complex.im atTop) (formal A P a χ m lam F) := by
  have hc : ContinuousAt (extend F.val) 0 :=
    (F.property.1.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (radius_pos a)))).continuousAt
  have ht : Tendsto (lift F) (comap Complex.im atTop) (𝓝 0) := by
    change Tendsto (extend F.val ∘ qParam 1) (comap Complex.im atTop) (𝓝 0)
    simpa only [F.property.2] using hc.tendsto.comp
      ((qParam_tendsto (by norm_num : (0 : ℝ) < 1)).mono_right nhdsWithin_le_nhds)
  apply ht.congr'
  have hIm : Tendsto Complex.im (comap Complex.im atTop) atTop := tendsto_comap
  filter_upwards [hIm.eventually (eventually_ge_atTop a)] with z hz
  exact (formal_above A P a χ m lam F hz).symm

/-- Once the exact Cauchy constraints hold, the periodic formal function
descends to a holomorphic function on the entire unit disk, vanishing at zero. -/
theorem formal_cusp_holomorphic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F)) :
    DifferentiableOn ℂ (cuspFunction 1 (formal A P a χ m lam F)) (ball 0 1) ∧
      cuspFunction 1 (formal A P a χ m lam F) 0 = 0 ∧
      ∀ z : ℂ, cuspFunction 1 (formal A P a χ m lam F) (qParam 1 z) =
        formal A P a χ m lam F z := by
  let G := formal A P a χ m lam F
  have hper := formal_periodic A P a χ m lam F
  have hzero := formal_zero_at_inf A P a χ m lam F
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} :=
    (FinitenessAllLevelCauchyConstraints.formal_identities_iff hN hp A P ha hae χ m lam F).mp he
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hevent : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ G z := by
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
    exact hG.differentiableAt (hopen.mem_nhds hz)
  refine ⟨?_, cuspFunction_zero_of_zero_at_inf (by norm_num) hzero,
    eq_cuspFunction (by norm_num) hper⟩
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact (differentiableAt_cuspFunction_zero (by norm_num) hper hevent
      hzero.boundedAtFilter).differentiableWithinAt
  · have him : 0 < (invQParam 1 w).im := by
      have hnorm : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
      rw [im_invQParam]
      have hlog : Real.log ‖w‖ < 0 := Real.log_neg (norm_pos_iff.mpr hw0) hnorm
      exact mul_pos_of_neg_of_neg
        (div_neg_of_neg_of_pos (by norm_num) (by positivity)) hlog
    have hd := differentiableAt_cuspFunction (by norm_num : (1 : ℝ) ≠ 0) hper
      (hG.differentiableAt (hopen.mem_nhds him))
    rw [qParam_right_inv (by norm_num) hw0] at hd
    exact hd.differentiableWithinAt

#print axioms formal_periodic
#print axioms formal_zero_at_inf
#print axioms formal_cusp_holomorphic

end FinitenessAllLevelFormalContinuation
