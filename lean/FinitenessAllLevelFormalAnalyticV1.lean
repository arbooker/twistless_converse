module

public import FinitenessAllLevelFormalRecoveryV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelReconstruction
  FinitenessAllLevelGoodTrace FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem step_differentiable (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ)
    (G : ℂ → ℂ → ℂ) (hG : ∀ w, Differentiable ℂ (fun lam => G lam w)) (z : ℂ) :
    Differentiable ℂ (fun lam => step A χ m lam (G lam) z) := by
  unfold step
  apply Differentiable.fun_sum
  intro i _
  apply (differentiable_const _).mul
  cases i with
  | inl i =>
      simp only [twoDilationRow, frickeRow, twist]
      apply (differentiable_const _).mul
      exact Differentiable.fun_sum (fun v _ => hG _)
  | inr i =>
      simp only [twoDilationRow, firstMultiplier]
      exact (((differentiable_const _).mul differentiable_id).mul (hG _)).sub
        ((differentiable_const _).mul (hG _))

theorem iterate_differentiable (A : Certificate N {p} Q hQ) (a : ℝ)
    (χ : ℕ → ℂ) (m : ℕ) (F : space (radius a)) (n : ℕ) (z : ℂ) :
    Differentiable ℂ (fun lam => iterate A a χ m lam F n z) := by
  induction n generalizing z with
  | zero => exact differentiable_const _
  | succ n ih =>
      by_cases hz : a ≤ z.im
      · simpa only [iterate, ite_eq_left hz] using
          (differentiable_const (lift F z) : Differentiable ℂ (fun _ : ℂ => lift F z))
      · simpa only [iterate, ite_eq_right hz] using
          step_differentiable A χ m (fun lam w => iterate A a χ m lam F n w) ih z

/-- The finite-depth formal continuation is entire in the retained
eigenvalue at every spatial point. Spatial holomorphy is not asserted. -/
theorem formal_differentiable (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (F : space (radius a)) (z : ℂ) :
    Differentiable ℂ (fun lam => formal A P a χ m lam F z) :=
  iterate_differentiable A a χ m F _ z

theorem formal_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (F : space (radius a)) (z : ℂ) :
    AnalyticOnNhd ℂ (fun lam => formal A P a χ m lam F z) Set.univ :=
  DifferentiableOn.analyticOnNhd (formal_differentiable A P a χ m F z).differentiableOn isOpen_univ

#print axioms iterate_differentiable
#print axioms formal_differentiable
#print axioms formal_analytic

end FinitenessAllLevelFormalContinuation
