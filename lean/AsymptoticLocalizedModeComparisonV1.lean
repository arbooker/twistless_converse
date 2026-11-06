module

public import AsymptoticCylinderModeAngleV1
public import AsymptoticCylinderUpperTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderModeComparison

open AsymptoticCylinder AsymptoticFourierNorm

theorem localized_mode_distance_sq_le (m t n : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (Y : ℝ) :
    ‖upperProjection Y (unitMode m t n hs hε - unitMode m 0 n hs hε)‖^2 ≤
      4 * (((2*t).factorial : ℝ) - 1) / ((m : ℝ)+1) := by
  apply le_trans _ (unitMode_distance_sq_le m t n hs hε)
  apply pow_le_pow_left₀ (norm_nonneg _)
  have hp : ‖upperProjection Y‖ ≤ 1 := AsymptoticRegionL2.projection_norm_le _ _ _
  exact ((upperProjection Y).le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg _))

theorem localized_mode_distance_sq_exp_le (m t n : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (Y : ℝ) :
    ‖upperProjection Y (unitMode m t n hs hε - unitMode m 0 n hs hε)‖^2 ≤
      Real.exp (((m : ℝ)+2*t+3)*Real.log 2 - (scale*Y/2)*(n+1:ℕ)) := by
  let v := upperProjection Y (unitMode m t n hs hε)
  let u := upperProjection Y (unitMode m 0 n hs hε)
  let E : ℝ := 2^(m+2*t+1)*Real.exp (-(scale*(n+1:ℕ)*Y/2))
  have hv : ‖v‖^2 ≤ E := by
    rw [show v = upperProjection Y (unitMode m t n hs hε) from rfl,
      upperProjection_unitMode_norm_sq]
    exact upperMass_le_exp m t (mul_pos hs (by positivity)) hε Y
  have hu : ‖u‖^2 ≤ E := by
    rw [show u = upperProjection Y (unitMode m 0 n hs hε) from rfl,
      upperProjection_unitMode_norm_sq]
    apply (upperMass_le_exp m 0 (mul_pos hs (by positivity)) hε Y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hdiff : ‖v-u‖^2 ≤ 4*E := by
    have hn := norm_sub_le v u
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖v‖-‖u‖)]
  rw [map_sub]
  apply hdiff.trans_eq
  have he : 4*E = 2^(m+2*t+3)*Real.exp (-(scale*(n+1:ℕ)*Y/2)) := by
    dsimp [E]
    rw [show m+2*t+3=(m+2*t+1)+2 by omega, pow_add]
    ring
  rw [he, show (2 : ℝ)^(m+2*t+3) = Real.exp (((m : ℝ)+2*t+3)*Real.log 2) by
    rw [show (m : ℝ)+2*t+3 = (m+2*t+3 : ℕ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)], ← Real.exp_add]
  congr 1
  ring

noncomputable def localizedErrorBound (t : ℕ) (scale Y : ℝ) : ℝ :=
  4 * (((2*t).factorial : ℝ) - 1) * (2*t+3) * Real.log 2 / (scale*Y/2) +
    1 / (1 - Real.exp (-(scale*Y/2)))

/-- Summing the squared localized differences costs O(1), independently
of the weight. The head uses the gamma estimate and the tail uses the
actual exponential Fourier-mass estimate. -/
theorem localized_mode_difference_summable_bound (m t : ℕ) {scale ε Y : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hY : 0 < Y) :
    Summable (fun n =>
      ‖upperProjection Y (unitMode m t n hs hε - unitMode m 0 n hs hε)‖^2) ∧
    (∑' n, ‖upperProjection Y (unitMode m t n hs hε - unitMode m 0 n hs hε)‖^2) ≤
      localizedErrorBound t scale Y := by
  let A : ℝ := 4 * (((2*t).factorial : ℝ) - 1)
  let a : ℝ := scale*Y/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hf : 1 ≤ ((2*t).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2*t)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨hsum, hbound⟩ := bounded_exp_summable_bound
    (fun n => ‖upperProjection Y (unitMode m t n hs hε - unitMode m 0 n hs hε)‖^2)
    ha (mul_nonneg (by positivity : 0 ≤ (m : ℝ)+2*t+3) hlog)
    (div_nonneg hA (by positivity : 0 ≤ (m : ℝ)+1))
    (fun _ => sq_nonneg _) (fun n => localized_mode_distance_sq_le m t n hs hε Y)
    (fun n => localized_mode_distance_sq_exp_le m t n hs hε Y)
  refine ⟨hsum, hbound.trans ?_⟩
  have hratio : ((m : ℝ)+2*t+3)/((m : ℝ)+1) ≤ 2*t+3 := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hh := mul_le_mul_of_nonneg_right hratio (div_nonneg (mul_nonneg hA hlog) ha.le)
  have he : A/((m : ℝ)+1) * (((m : ℝ)+2*t+3)*Real.log 2/a) =
      (((m : ℝ)+2*t+3)/((m : ℝ)+1)) * (A*Real.log 2/a) := by ring
  rw [he]
  change _ ≤ A*(2*t+3)*Real.log 2/a + 1/(1-Real.exp (-a))
  calc
    _ ≤ (2*t+3)*(A*Real.log 2/a) + 1/(1-Real.exp (-a)) := add_le_add hh le_rfl
    _ = _ := by ring

#print axioms localized_mode_distance_sq_exp_le
#print axioms localized_mode_difference_summable_bound

end AsymptoticCylinderModeComparison
