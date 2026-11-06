module

public import AsymptoticWeightedProjectionTraceV1
public import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderModeComparison

open AsymptoticCylinder Filter
open scoped Topology

noncomputable def massSlope (t : ℕ) (scale Y : ℝ) : ℝ :=
  (2*t+1)*Real.log 2/(scale*Y/2) + 1/(1-Real.exp (-(scale*Y/2)))

theorem massBound_le_linear (m t : ℕ) {scale Y : ℝ} (hs : 0 < scale) (hY : 0 < Y) :
    massBound m t scale Y ≤ massSlope t scale Y * ((m : ℝ)+2) := by
  have ha : 0 < scale*Y/2 := by positivity
  have hc : 0 ≤ Real.log 2/(scale*Y/2) :=
    div_nonneg (Real.log_nonneg (by norm_num)) ha.le
  have hd : 0 ≤ 1/(1-Real.exp (-(scale*Y/2))) :=
    div_nonneg zero_le_one (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  have hcoef : (m : ℝ)+2*t+1 ≤ (2*t+1)*((m : ℝ)+2) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hmain := mul_le_mul_of_nonneg_right hcoef hc
  have htail := mul_le_mul_of_nonneg_left
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith : 1 ≤ (m : ℝ)+2) hd
  unfold massBound massSlope
  push_cast
  convert add_le_add hmain htail using 1 <;> ring

theorem massSlope_nonneg (t : ℕ) {scale Y : ℝ} (hs : 0 < scale) (hY : 0 < Y) :
    0 ≤ massSlope t scale Y := by
  have ha : 0 < scale*Y/2 := by positivity
  have hd : 0 < 1-Real.exp (-(scale*Y/2)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold massSlope
  exact add_nonneg (div_nonneg (mul_nonneg (by positivity)
    (Real.log_nonneg (by norm_num))) ha.le) (by positivity)

theorem massSlope_zero_le (t : ℕ) (scale Y : ℝ) (ha : 0 < scale*Y/2) :
    massSlope 0 scale Y ≤ massSlope t scale Y := by
  unfold massSlope
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ ha.le
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  norm_num

/-- A bound uniform over all operators of norm at most B; localization
and the fixed weight are chosen before the weight index m varies. -/
theorem normalized_localizedTrace_difference_bound (m t : ℕ) {scale ε Y B : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hY : 0 < Y) (W : Space →L[ℂ] Space)
    (hW : ‖W‖ ≤ B) :
    ‖(localizedTrace m t hs hε Y W - localizedTrace m 0 hs hε Y W) / ((m : ℝ)+2)‖ ≤
      (2*B*Real.sqrt (localizedErrorBound t scale Y)*Real.sqrt (massSlope t scale Y)) *
        (Real.sqrt ((m : ℝ)+2))⁻¹ := by
  have hB : 0 ≤ B := (norm_nonneg W).trans hW
  have hK : 0 < (m : ℝ)+2 := by positivity
  have hA := massSlope_nonneg t hs hY
  have hmass : massBound m 0 scale Y ≤ massSlope t scale Y*((m : ℝ)+2) :=
    (massBound_le_linear m 0 hs hY).trans
      (mul_le_mul_of_nonneg_right (massSlope_zero_le t scale Y (by positivity)) hK.le)
  have h1 := Real.sqrt_le_sqrt (massBound_le_linear m t hs hY)
  have h0 := Real.sqrt_le_sqrt hmass
  rw [Real.sqrt_mul hA] at h1 h0
  have hh := localizedTrace_difference_bound m t hs hε hY W
  have hb : ‖localizedTrace m t hs hε Y W - localizedTrace m 0 hs hε Y W‖ ≤
      (2*B*Real.sqrt (localizedErrorBound t scale Y)*Real.sqrt (massSlope t scale Y)) *
        Real.sqrt ((m : ℝ)+2) := by
    apply hh.trans
    apply (mul_le_mul
      (mul_le_mul_of_nonneg_right hW (Real.sqrt_nonneg _)) (add_le_add h1 h0)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hB (Real.sqrt_nonneg _))).trans_eq
    ring
  rw [norm_div, Real.norm_of_nonneg hK.le]
  apply (div_le_div_of_nonneg_right hb hK.le).trans_eq
  rw [mul_div_assoc, Real.sqrt_div_self]

/-- Replacing the weighted projection by the unweighted projection costs
o(k) for every uniformly bounded family of localized operators. -/
theorem localizedTrace_difference_isLittleO (t : ℕ) {scale ε Y B : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hY : 0 < Y) (W : ℕ → Space →L[ℂ] Space)
    (hW : ∀ m, ‖W m‖ ≤ B) :
    (fun m => localizedTrace m t hs hε Y (W m) - localizedTrace m 0 hs hε Y (W m))
      =o[atTop] (fun m : ℕ => (m : ℝ)+2) := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun m hm => by
    have : (0 : ℝ) < (m : ℝ)+2 := by positivity
    exact False.elim (this.ne' hm))).mpr
  have hi : Tendsto (fun m : ℕ => (Real.sqrt ((m : ℝ)+2))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop))
  have hl := hi.const_mul
    (2*B*Real.sqrt (localizedErrorBound t scale Y)*Real.sqrt (massSlope t scale Y))
  simp only [mul_zero] at hl
  exact squeeze_zero_norm (fun m => normalized_localizedTrace_difference_bound m t hs hε hY (W m) (hW m)) hl

#print axioms normalized_localizedTrace_difference_bound
#print axioms localizedTrace_difference_isLittleO

end AsymptoticCylinderModeComparison
