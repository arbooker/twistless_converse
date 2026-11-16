module

public import QuantitativeMaassWaveSeedPropagationV1
public import QuantitativeArithmeticMaassTruncatedLogV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassModularHeight

theorem logarithmicCuspCutoff_real (N : ℕ) (R : ℝ) (hR : 0≤R) (Z : ℍ) :
    (upperFunction (logarithmicCuspCutoff N R hR).value Z).re=truncatedLog R (height Z) := by
  change (upperFunction (profile (fun y => (truncatedLog R y:ℂ))) Z).re=_
  rw [upper_profile,Complex.ofReal_re]

/-- Genuine height propagation from the constructed logarithmic separator.
There is no separating-weight hypothesis in this statement. -/
theorem poincare_wave_above_height (N : ℕ) (u : SmoothUpperSeed) {Y H : ℝ}
    (hY : 3≤Y) (hYH : Y≤H)
    (hu : ∀ Z : ℍ, Y<height Z → upperFunction u.toFun Z=0)
    (t : ℝ) (ht : |t|<Real.log (H/Y)) :
    ∀ᵐ Z ∂quotientMeasure N, H≤height Z →
      (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val Z=0 := by
  let R := H+1
  have hR : 0≤R := by dsimp [R]; linarith
  let b := logarithmicCuspCutoff N R hR
  have hs : ∀ Z : ℍ, truncatedLog R Y<(upperFunction b.value Z).re →
      upperFunction u.toFun Z=0 := by
    intro Z hZ
    apply hu Z
    by_contra hn
    have hm := truncatedLog_monotone R (le_of_not_gt hn)
    rw [logarithmicCuspCutoff_real] at hZ
    exact (not_le.mpr hZ) hm
  have hw := poincare_wave_weighted_support N b u (truncatedLog R Y) hs t
  have hd : truncatedLog R H-truncatedLog R Y=Real.log (H/Y) :=
    truncatedLog_sub_eq_log R hY hYH (by dsimp [R]; linarith)
  filter_upwards [hw] with Z hZ
  intro hHZ
  apply hZ
  rw [logarithmicCuspCutoff_real]
  change truncatedLog R Y+|1| * |t|<truncatedLog R (height Z)
  have hm := truncatedLog_monotone R hHZ
  norm_num only [abs_one,one_mul]
  linarith

/-- The sharp exponential cusp-height front for the actual quotient wave.
The countable rational-threshold argument retains all AE qualifications. -/
theorem poincare_wave_height_support (N : ℕ) (u : SmoothUpperSeed) {Y : ℝ} (hY : 3≤Y)
    (hu : ∀ Z : ℍ, Y<height Z → upperFunction u.toFun Z=0) (t : ℝ) :
    ∀ᵐ Z ∂quotientMeasure N, Y*Real.exp |t|<height Z →
      (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val Z=0 := by
  have hYpos : 0<Y := by linarith
  have hfront : Y≤Y*Real.exp |t| := by
    have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg t)) hYpos.le
    simpa only [mul_one] using hm
  have hq : ∀ q : ℚ, ∀ᵐ Z ∂quotientMeasure N,
      Y*Real.exp |t|<(q:ℝ) → (q:ℝ)≤height Z →
        (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val Z=0 := by
    intro q
    by_cases hq : Y*Real.exp |t|<(q:ℝ)
    · have hYq : Y≤(q:ℝ) := hfront.trans hq.le
      have hlog : |t|<Real.log ((q:ℝ)/Y) := by
        apply (Real.lt_log_iff_exp_lt (div_pos (hYpos.trans_le hYq) hYpos)).mpr
        apply (lt_div_iff₀ hYpos).mpr
        simpa only [mul_comm] using hq
      filter_upwards [poincare_wave_above_height N u hY hYq hu t hlog] with Z hZ
      exact fun _ => hZ
    · exact Eventually.of_forall (fun _ h => False.elim (hq h))
  filter_upwards [ae_all_iff.mpr hq] with Z hZ
  intro hout
  obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hout
  exact hZ q hq₁ hq₂.le

#print axioms poincare_wave_above_height
#print axioms poincare_wave_height_support

end QuantitativeMaass.Weighted
