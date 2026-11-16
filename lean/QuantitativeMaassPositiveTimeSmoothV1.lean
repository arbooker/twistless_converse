module

public import QuantitativeMaassPositiveTimeRemainderV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass

local instance (N : ℕ) :
    ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

/-- Differentiability is in operator norm, on the open range of translations
whose test support stays away from zero. -/
theorem translatedPositiveTimeAbelOperator_hasDerivAt (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (x : ℝ) (hx : 0<ψ.left+x) :
    HasDerivAt (translatedPositiveTimeAbelOperator N ψ)
      (-translatedPositiveTimeAbelOperator N ψ.first x) x := by
  have hd := (contDiff_infty_iff_deriv.mp ψ.first.smooth).2
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    ψ.compact.deriv.deriv hd (by simp)
  apply (HasDerivAt.of_isLittleO (f := translatedPositiveTimeAbelOperator N ψ)
    (f' := -translatedPositiveTimeAbelOperator N ψ.first x) (x := x))
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let A := positiveTimeNormConstant ((ψ.left+x)/2) (ψ.right+|x|+(ψ.left+x)/2)
  let M : ℝ := A*(K:ℝ)
  have hA : 0≤A := positiveTimeNormConstant_nonneg _ _ (by linarith)
  have hM : 0≤M := mul_nonneg hA K.coe_nonneg
  have hpos : 0<M+1 := by linarith
  have hrad : 0<min ((ψ.left+x)/2) (ε/(M+1)) := lt_min (by linarith) (div_pos hε hpos)
  filter_upwards [Metric.ball_mem_nhds x hrad] with z hz
  have hz' : ‖z-x‖<min ((ψ.left+x)/2) (ε/(M+1)) :=
    by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hnear : |z-x|<(ψ.left+x)/2 := by simpa only [Real.norm_eq_abs] using (lt_min_iff.mp hz').1
  have hsmall : M*‖z-x‖≤ε := by
    have h := (lt_div_iff₀ hpos).mp (lt_min_iff.mp hz').2
    nlinarith [norm_nonneg (z-x)]
  calc
    _ ≤ M*‖z-x‖^2 := by
      simpa only [M,A,mul_assoc] using
        translatedPositiveTimeAbelOperator_remainder_le N ψ K hK x hx z hnear
    _ ≤ ε*‖z-x‖ := by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (z-x))]

/-- Repeated time translation is smooth in the actual operator norm. -/
theorem translatedPositiveTimeAbelOperator_contDiffOn_nat (n : ℕ) (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) :
    ContDiffOn ℝ n (translatedPositiveTimeAbelOperator N ψ) (Ioi (-ψ.left)) := by
  induction n generalizing ψ with
  | zero =>
    rw [Nat.cast_zero,contDiffOn_zero]
    intro x hx
    exact (translatedPositiveTimeAbelOperator_hasDerivAt N ψ x (by have := hx; simp only [mem_Ioi] at this; linarith)).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨?_,by simp,?_⟩
    · intro x hx
      exact (translatedPositiveTimeAbelOperator_hasDerivAt N ψ x (by have := hx; simp only [mem_Ioi] at this; linarith)).differentiableAt.differentiableWithinAt
    · apply (ih ψ.first).neg.congr
      intro x hx
      exact (translatedPositiveTimeAbelOperator_hasDerivAt N ψ x (by have := hx; simp only [mem_Ioi,PositiveTimeTest.first] at this; linarith)).deriv

theorem translatedPositiveTimeAbelOperator_smooth (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) :
    ContDiffOn ℝ ∞ (translatedPositiveTimeAbelOperator N ψ) (Ioi (-ψ.left)) :=
  contDiffOn_infty.mpr (fun n => translatedPositiveTimeAbelOperator_contDiffOn_nat n N ψ)

#print axioms translatedPositiveTimeAbelOperator_hasDerivAt
#print axioms translatedPositiveTimeAbelOperator_smooth

end QuantitativeMaass
