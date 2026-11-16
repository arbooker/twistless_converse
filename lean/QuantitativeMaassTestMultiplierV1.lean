module

public import QuantitativeMaassPositiveUnitTestV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- Multiplication by a smooth scalar function preserves the positive test
space and is continuous for its LF topology. -/
def positiveTestMultiplier (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    PositiveSmoothTest →L[ℝ] PositiveSmoothTest :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hρ

theorem positiveTestMultiplier_apply (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (φ : PositiveSmoothTest) (t : ℝ) : positiveTestMultiplier ρ hρ φ t=φ t*ρ t := rfl

theorem positiveTestMultiplier_deriv (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (φ : PositiveSmoothTest) :
    positiveSmoothTestDeriv (positiveTestMultiplier ρ hρ φ)=
      positiveTestMultiplier ρ hρ (positiveSmoothTestDeriv φ)+
        positiveTestMultiplier (deriv ρ) (contDiff_infty_iff_deriv.mp hρ).2 φ := by
  ext t
  change deriv (fun t => φ t*ρ t) t=_
  have hd := ((φ.contDiff.differentiable (by simp) t).hasDerivAt).mul
    ((hρ.differentiable (by simp) t).hasDerivAt)
  have he : HasDerivAt (fun t => φ t*ρ t)
      (deriv (φ : ℝ → ℝ) t*ρ t+φ t*deriv ρ t) t := by
    convert! hd using 1
  change deriv (fun t => φ t*ρ t) t=positiveSmoothTestDeriv φ t*ρ t+φ t*deriv ρ t
  rw [positiveSmoothTestDeriv_apply]
  exact he.deriv

def positiveTestPower (n : ℕ) : PositiveSmoothTest →L[ℝ] PositiveSmoothTest :=
  positiveTestMultiplier (fun t => t^n) (contDiff_id.pow n)

theorem positiveTestPower_apply (n : ℕ) (φ : PositiveSmoothTest) (t : ℝ) :
    positiveTestPower n φ t=φ t*t^n := rfl

theorem positiveTestPower_zero (φ : PositiveSmoothTest) : positiveTestPower 0 φ=φ := by
  ext t
  simp only [positiveTestPower_apply,pow_zero,mul_one]

theorem positiveTestPower_deriv_succ (n : ℕ) (φ : PositiveSmoothTest) :
    positiveSmoothTestDeriv (positiveTestPower (n+1) φ)=
      positiveTestPower (n+1) (positiveSmoothTestDeriv φ)+(n+1:ℝ) • positiveTestPower n φ := by
  ext t
  rw [positiveSmoothTestDeriv_apply]
  change deriv (fun t => φ t*t^(n+1)) t=_
  have hp : HasDerivAt (fun s : ℝ => s^(n+1)) ((n+1:ℝ)*t^n) t := by
    convert! (hasDerivAt_id t).pow (n+1) using 1
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq]
  have hd := ((φ.contDiff.differentiable (by simp) t).hasDerivAt).mul hp
  change deriv (fun t => φ t*t^(n+1)) t=
    positiveSmoothTestDeriv φ t*t^(n+1)+(n+1:ℝ)*(φ t*t^n)
  rw [positiveSmoothTestDeriv_apply]
  convert! hd.deriv using 1
  ring

/-- Polynomial moments of a first-order distribution equation satisfy an
exact recurrence. This is the algebra behind the bounded integrating factor. -/
theorem positiveDistribution_moment_recurrence {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →ₗ[ℝ] H)
    (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ))
    (n : ℕ) (φ : PositiveSmoothTest) :
    T (positiveTestPower (n+1) (positiveSmoothTestDeriv φ))=
      B (T (positiveTestPower (n+1) φ))-(n+1:ℝ) • T (positiveTestPower n φ) := by
  have h := hT (positiveTestPower (n+1) φ)
  rw [positiveTestPower_deriv_succ,map_add,map_smul] at h
  exact eq_sub_of_add_eq h

#print axioms positiveTestMultiplier_deriv
#print axioms positiveTestPower_deriv_succ
#print axioms positiveDistribution_moment_recurrence

end QuantitativeMaass
