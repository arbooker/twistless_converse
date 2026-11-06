module

public import AsymptoticGammaTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticGammaMoments

open MeasureTheory Set AsymptoticGammaTail

/-- Moments of the gamma variable divided by its mean. -/
noncomputable def moment (K : ℝ) (u : ℕ) : ℝ :=
  ∏ j ∈ Finset.range u, (1 + (j : ℝ) / K)

theorem moment_zero (K : ℝ) : moment K 0 = 1 := by simp [moment]

theorem moment_succ (K : ℝ) (u : ℕ) :
    moment K (u+1) = moment K u * (1 + (u : ℝ) / K) := by
  simp [moment, Finset.prod_range_succ]

theorem moment_one_le {K : ℝ} (hK : 0 < K) (u : ℕ) : 1 ≤ moment K u := by
  induction u with
  | zero => simp [moment_zero]
  | succ u ih =>
    rw [moment_succ]
    exact one_le_mul_of_one_le_of_one_le ih (by
      have : 0 ≤ (u : ℝ) / K := by positivity
      linarith)

/-- A deliberately coarse bound, uniform in the gamma shape. Its constant
depends only on the fixed moment order. -/
theorem moment_sub_one_le {K : ℝ} (hK : 1 ≤ K) (u : ℕ) :
    moment K u - 1 ≤ ((u.factorial : ℝ) - 1) / K := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  induction u with
  | zero => simp [moment_zero]
  | succ u ih =>
    have hf : 1 ≤ (u.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos u
    have hcoef : 0 ≤ 1 + (u : ℝ) / K := by positivity
    have hb := mul_le_mul_of_nonneg_right ih hcoef
    have hsmall : ((u.factorial : ℝ) - 1) / K ≤ (u.factorial : ℝ) - 1 :=
      (div_le_iff₀ hK0).mpr (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ (u : ℝ) / K)
    rw [moment_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hcancel : ((u.factorial : ℝ) - 1) / K +
        (u : ℝ) / K + ((u.factorial : ℝ) - 1) * ((u : ℝ) / K) =
        (((u : ℝ) + 1) * (u.factorial : ℝ) - 1) / K := by ring
    nlinarith

theorem kernel_power (m u : ℕ) (r y : ℝ) :
    y ^ u * kernel m r y = kernel (m+u) r y := by
  simp only [kernel, pow_add]
  ring

theorem integral_kernel_pos (m : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < ∫ y in Ioi 0, kernel m r y := by
  rw [integral_kernel m hr]
  positivity

/-- The integer gamma recurrence, retaining the actual radial integrals. -/
theorem normalized_integral_moment (m u : ℕ) {r : ℝ} (hr : 0 < r) :
    ((r / ((m : ℝ)+1)) ^ u * (∫ y in Ioi 0, kernel (m+u) r y)) /
      (∫ y in Ioi 0, kernel m r y) = moment ((m : ℝ)+1) u := by
  have hr0 : r ≠ 0 := hr.ne'
  have hm0 : (m : ℝ)+1 ≠ 0 := by positivity
  have hf0 : (m.factorial : ℝ) ≠ 0 := by positivity
  simp only [integral_kernel _ hr]
  induction u with
  | zero => simp [moment_zero, hf0, hr0]
  | succ u ih =>
    rw [moment_succ, ← ih]
    rw [show m+(u+1)=(m+u)+1 by omega, Nat.factorial_succ]
    push_cast
    simp only [pow_succ]
    field_simp
    ring

theorem normalized_power_integrable (m u : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => (r*y/((m : ℝ)+1)) ^ u * kernel m r y)
      (volume.restrict (Ioi 0)) := by
  have he : (fun y => (r*y/((m : ℝ)+1)) ^ u * kernel m r y) =
      (fun y => (r/((m : ℝ)+1)) ^ u * kernel (m+u) r y) := by
    funext y
    rw [← kernel_power]
    ring
  rw [he]
  exact (integrable_kernel (m+u) hr).const_mul _

theorem normalized_power_integral (m u : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ y in Ioi 0, (r*y/((m : ℝ)+1)) ^ u * kernel m r y) =
      moment ((m : ℝ)+1) u * (∫ y in Ioi 0, kernel m r y) := by
  have he : (fun y => (r*y/((m : ℝ)+1)) ^ u * kernel m r y) =
      (fun y => (r/((m : ℝ)+1)) ^ u * kernel (m+u) r y) := by
    funext y
    rw [← kernel_power]
    ring
  rw [he, integral_const_mul]
  exact (div_eq_iff (integral_kernel_pos m hr).ne').mp (normalized_integral_moment m u hr)

theorem squared_error_integrable (m t : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => ((r*y/((m : ℝ)+1)) ^ t - 1)^2 * kernel m r y)
      (volume.restrict (Ioi 0)) := by
  have h := ((normalized_power_integrable m (2*t) hr).sub
    ((normalized_power_integrable m t hr).const_mul 2)).add (integrable_kernel m hr)
  apply h.congr
  filter_upwards [] with y
  dsimp
  rw [show 2*t=t*2 by omega, pow_mul]
  ring

/-- The quantitative O_t(1/K) gamma estimate in the weighted projection
comparison, with K=m+1. This is an estimate of the actual radial integral. -/
theorem squared_error_bound (m t : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ y in Ioi 0, ((r*y/((m : ℝ)+1)) ^ t - 1)^2 * kernel m r y) /
      (∫ y in Ioi 0, kernel m r y) ≤
      (((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1) := by
  have hK : 0 < (m : ℝ)+1 := by positivity
  have hmass := integral_kernel_pos m hr
  have he : (fun y => ((r*y/((m : ℝ)+1)) ^ t - 1)^2 * kernel m r y) =
      (fun y => (r*y/((m : ℝ)+1)) ^ (2*t) * kernel m r y -
        2*((r*y/((m : ℝ)+1)) ^ t * kernel m r y) + kernel m r y) := by
    funext y
    rw [show 2*t=t*2 by omega, pow_mul]
    ring
  have hf : Integrable (fun y => (r*y/((m : ℝ)+1)) ^ (2*t) * kernel m r y -
      2*((r*y/((m : ℝ)+1)) ^ t * kernel m r y)) (volume.restrict (Ioi 0)) := by
    apply ((normalized_power_integrable m (2*t) hr).sub
      ((normalized_power_integrable m t hr).const_mul 2)).congr
    filter_upwards [] with y
    dsimp
  rw [he, integral_add hf (integrable_kernel m hr),
    integral_sub (normalized_power_integrable m (2*t) hr)
      ((normalized_power_integrable m t hr).const_mul 2), integral_const_mul,
    normalized_power_integral m (2*t) hr, normalized_power_integral m t hr]
  have hid : (moment ((m : ℝ)+1) (2*t) * (∫ y in Ioi 0, kernel m r y) -
      2*(moment ((m : ℝ)+1) t * (∫ y in Ioi 0, kernel m r y)) +
      (∫ y in Ioi 0, kernel m r y)) / (∫ y in Ioi 0, kernel m r y) =
      moment ((m : ℝ)+1) (2*t) - 2*moment ((m : ℝ)+1) t + 1 := by
    field_simp [hmass.ne']
  rw [hid]
  have h1 := moment_one_le hK t
  have h2 := moment_sub_one_le (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith : 1 ≤ (m : ℝ)+1) (2*t)
  linarith

#print axioms moment_sub_one_le
#print axioms normalized_integral_moment
#print axioms squared_error_bound

end AsymptoticGammaMoments
