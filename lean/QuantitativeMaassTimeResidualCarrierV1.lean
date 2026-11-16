module

public import QuantitativeMaassHigherTimeCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/- Min-owned draft: not compiler-verified when written. -/

/-- The residual at spectral centre t of a carrier with phase frequency τ.
Keeping the two frequencies distinct retains the cancellation for a window
whose endpoints are t and t+ε. -/
def timeResidualCarrier (t τ : ℝ) (A : ℝ → ℂ) (s : ℝ) : ℂ :=
  ((τ : ℂ)^2 - (t : ℂ)^2) * A s -
    (2*(τ : ℂ)*Complex.I) * deriv A s - deriv (deriv A) s

theorem timeResidualCarrier_smooth (t τ : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (timeResidualCarrier t τ A) := by
  have hA1 := (contDiff_infty_iff_deriv.mp hA).2
  have hA2 := (contDiff_infty_iff_deriv.mp hA1).2
  unfold timeResidualCarrier
  fun_prop

/-- The residual amplitude keeps the same closed support interval. -/
theorem timeResidualCarrier_support (t τ : ℝ) (A : ℝ → ℂ) (L : ℝ)
    (hs : Function.support A ⊆ Icc (-L) L) :
    Function.support (timeResidualCarrier t τ A) ⊆ Icc (-L) L := by
  have hs1 : Function.support (deriv A) ⊆ Icc (-L) L :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Icc)
  have hs2 : Function.support (deriv (deriv A)) ⊆ Icc (-L) L :=
    support_deriv_subset.trans (closure_minimal hs1 isClosed_Icc)
  intro s hn
  by_contra hout
  have h0 : A s = 0 := by by_contra h; exact hout (hs h)
  have h1 : deriv A s = 0 := by by_contra h; exact hout (hs1 h)
  have h2 : deriv (deriv A) s = 0 := by by_contra h; exact hout (hs2 h)
  exact hn (by simp only [timeResidualCarrier, h0, h1, h2, mul_zero, sub_self])

/-- The exact residual has no uncancelled τ² term when τ=t. -/
theorem timeFrequencyShift_residual (t τ : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) :
    (fun s => -deriv (deriv (timeFrequencyShift τ A)) s -
      (t : ℂ)^2 * timeFrequencyShift τ A s) =
        timeFrequencyShift τ (timeResidualCarrier t τ A) := by
  rw [timeFrequencyShift_deriv τ A hA,
    timeFrequencyShift_deriv τ (timeDerivativeCarrier τ A)
      (timeDerivativeCarrier_smooth τ A hA)]
  funext s
  change -(Complex.exp ((τ*s : ℝ)*Complex.I) *
      ((τ : ℂ)*Complex.I*timeDerivativeCarrier τ A s +
        deriv (timeDerivativeCarrier τ A) s)) -
      (t : ℂ)^2 * (Complex.exp ((τ*s : ℝ)*Complex.I)*A s) = _
  rw [timeDerivativeCarrier_deriv τ A hA]
  simp only [timeFrequencyShift, timeResidualCarrier, timeDerivativeCarrier,
    iteratedDeriv_succ, iteratedDeriv_zero]
  ring_nf
  simp [Complex.I_sq]

/-- Derivatives fall only on the slow amplitude after the quadratic
spectral cancellation has been performed. -/
theorem timeResidualCarrier_iterated (t τ : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (n : ℕ) (s : ℝ) :
    iteratedDeriv n (timeResidualCarrier t τ A) s =
      ((τ : ℂ)^2 - (t : ℂ)^2) * iteratedDeriv n A s -
        (2*(τ : ℂ)*Complex.I) * iteratedDeriv (n+1) A s -
        iteratedDeriv (n+2) A s := by
  have hA1 := (contDiff_infty_iff_deriv.mp hA).2
  have hA2 := (contDiff_infty_iff_deriv.mp hA1).2
  have hn0 : ContDiffAt ℝ n A s := (hA.of_le (by simp)).contDiffAt
  have hn1 : ContDiffAt ℝ n (deriv A) s := (hA1.of_le (by simp)).contDiffAt
  have hn2 : ContDiffAt ℝ n (deriv (deriv A)) s := (hA2.of_le (by simp)).contDiffAt
  have hc0 : ContDiffAt ℝ n (fun x => ((τ : ℂ)^2-(t : ℂ)^2)*A x) s :=
    contDiffAt_const.mul hn0
  have hc1 : ContDiffAt ℝ n (fun x => (2*(τ : ℂ)*Complex.I)*deriv A x) s :=
    contDiffAt_const.mul hn1
  calc
    _ = iteratedDeriv n (fun x => ((τ : ℂ)^2-(t : ℂ)^2)*A x -
          (2*(τ : ℂ)*Complex.I)*deriv A x) s -
          iteratedDeriv n (deriv (deriv A)) s :=
      iteratedDeriv_sub (hc0.sub hc1) hn2
    _ = (iteratedDeriv n (fun x => ((τ : ℂ)^2-(t : ℂ)^2)*A x) s -
          iteratedDeriv n (fun x => (2*(τ : ℂ)*Complex.I)*deriv A x) s) -
          iteratedDeriv n (deriv (deriv A)) s :=
      congrArg (fun z => z - iteratedDeriv n (deriv (deriv A)) s)
        (iteratedDeriv_sub hc0 hc1)
    _ = _ := by
      rw [iteratedDeriv_const_mul _ hn0, iteratedDeriv_const_mul _ hn1,
        ← iteratedDeriv_succ', ← iteratedDeriv_succ', ← iteratedDeriv_succ']

/-- Finite-order residual amplitude bounds preserve the quadratic
cancellation and require only two additional derivatives of the amplitude. -/
theorem timeResidualCarrier_iterated_bound (t τ : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (m : ℕ) (M : ℝ)
    (hb : ∀ n : ℕ, n ≤ m+2 → ∀ s, ‖iteratedDeriv n A s‖ ≤ M) :
    ∀ n : ℕ, n ≤ m → ∀ s,
      ‖iteratedDeriv n (timeResidualCarrier t τ A) s‖ ≤
        (|τ^2-t^2| + 2*|τ| + 1)*M := by
  have hc : ‖(τ : ℂ)^2-(t : ℂ)^2‖ = |τ^2-t^2| := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  intro n hn s
  rw [timeResidualCarrier_iterated t τ A hA n s]
  calc
    _ ≤ (‖((τ : ℂ)^2-(t : ℂ)^2)*iteratedDeriv n A s‖ +
        ‖(2*(τ : ℂ)*Complex.I)*iteratedDeriv (n+1) A s‖) +
        ‖iteratedDeriv (n+2) A s‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = |τ^2-t^2| *‖iteratedDeriv n A s‖ +
        2*|τ| *‖iteratedDeriv (n+1) A s‖ + ‖iteratedDeriv (n+2) A s‖ := by
      simp only [norm_mul, hc, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]
    _ ≤ |τ^2-t^2| *M + 2*|τ| *M + M :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hb n (by omega) s) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hb (n+1) (by omega) s) (by positivity)))
        (hb (n+2) (by omega) s)
    _ = _ := by ring

/-- A one-sided window's actual phase centre differs from its left
endpoint by ε/2; this costs only linear growth in t. -/
theorem timeResidualCarrier_window_coefficient (t ε : ℝ)
    (ht : 1 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(t+ε/2)^2-t^2| + 2*|t+ε/2| + 1 ≤ 6*t := by
  have ht0 : 0 ≤ t := by linarith
  have he2 : ε^2 ≤ 1 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1)]
  have hte : t*ε ≤ t := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hε1)]
  rw [abs_of_nonneg (by nlinarith [mul_nonneg ht0 hε] : 0 ≤ (t+ε/2)^2-t^2),
    abs_of_nonneg (by linarith : 0 ≤ t+ε/2)]
  nlinarith

theorem timeResidualCarrier_negative_window_coefficient (t ε : ℝ)
    (ht : 1 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(-(t+ε/2))^2-t^2| + 2*|-(t+ε/2)| + 1 ≤ 6*t := by
  simpa only [neg_sq, abs_neg] using timeResidualCarrier_window_coefficient t ε ht hε hε1

#print axioms timeFrequencyShift_residual
#print axioms timeResidualCarrier_iterated_bound
#print axioms timeResidualCarrier_window_coefficient

end QuantitativeMaass
