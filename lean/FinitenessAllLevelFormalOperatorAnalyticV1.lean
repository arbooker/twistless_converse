module

public import FinitenessAllLevelFormalOperatorV1
public import FinitenessAllLevelAnalyticSubstitutionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGoodTrace FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem stepOperator_differentiable (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ)
    (G : ℂ → ℂ → X →L[ℂ] ℂ) (hG : ∀ w, Differentiable ℂ (fun lam => G lam w)) (z : ℂ) :
    Differentiable ℂ (fun lam => stepOperator A χ m lam (G lam) z) := by
  let : IsBoundedSMul ℂ (X →L[ℂ] ℂ) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  unfold stepOperator
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.fun_smul (𝕜 := ℂ) (𝕜' := ℂ) (F := X →L[ℂ] ℂ) (differentiable_const _)
  cases i with
  | inl i =>
      simp only [rowOperator]
      apply Differentiable.fun_smul (𝕜 := ℂ) (𝕜' := ℂ) (F := X →L[ℂ] ℂ) (differentiable_const _)
      exact Differentiable.fun_sum (fun v _ => hG _)
  | inr i =>
      simp only [rowOperator, firstMultiplier]
      exact (((differentiable_const _).mul differentiable_id).fun_smul (hG _)).sub
        ((differentiable_const _).fun_smul (hG _))

theorem iterateOperator_differentiable (A : Certificate N {p} Q hQ) (a : ℝ)
    (χ : ℕ → ℂ) (m : ℕ) (n : ℕ) (z : ℂ) :
    Differentiable ℂ (fun lam => iterateOperator A a χ m lam n z) := by
  induction n generalizing z with
  | zero => exact differentiable_const _
  | succ n ih =>
      by_cases hz : a ≤ z.im
      · simpa only [iterateOperator, ite_eq_left hz] using
          (differentiable_const (initialOperator a z) :
            Differentiable ℂ (fun _ : ℂ => initialOperator a z))
      · simpa only [iterateOperator, ite_eq_right hz] using
          stepOperator_differentiable A χ m (fun lam w => iterateOperator A a χ m lam n w) ih z

/-- Entire dependence in operator norm, stronger than pointwise entire
dependence after fixing the initial function. -/
theorem formalOperator_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun lam => formalOperator A P a χ m lam z) Set.univ :=
  DifferentiableOn.analyticOnNhd
    (iterateOperator_differentiable A a χ m (depth A P a z) z).differentiableOn isOpen_univ

/-- Each spatial evaluation of the formal continuation is a holomorphic
function of the eigenvalue and initial Banach-disk input jointly. This does
not yet assert measurability or local uniform bounds in the spatial variable. -/
theorem formal_joint_analytic (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun t : ℂ × space (radius a) => formal A P a χ m t.1 t.2 z) Set.univ := by
  have hh := FinitenessAllLevelAnalyticSubstitution.joint_analytic
    (formalOperator_analytic A P a χ m z)
  simpa only [Set.univ_prod_univ, formalOperator_apply] using hh

#print axioms iterateOperator_differentiable
#print axioms formalOperator_analytic
#print axioms formal_joint_analytic

end FinitenessAllLevelFormalContinuation
