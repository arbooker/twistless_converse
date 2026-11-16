module
public import QuantitativeArithmeticMaassTruncatedLogV1
public import QuantitativeMaassWaveLocalizedPropagationV1
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology
namespace QuantitativeArithmeticMaassModularHeight
open QuantitativeMaass QuantitativeMaass.Weighted

theorem logarithmicCuspCutoff_upper (N : ℕ) (R : ℝ) (hR : 0≤R) (z : ℍ) :
    (upperFunction (logarithmicCuspCutoff N R hR).value z).re=
      truncatedLog R (height z) := by
  change (upperFunction (profile (fun y => (truncatedLog R y : ℂ))) z).re=_
  rw [upper_profile]
  rfl

/-- Sharp finite propagation between truncated modular-height regions.
The separating weight is explicitly constructed, rather than supplied as
an additional hypothesis. The input can be any quotient L2 vector. -/
theorem height_localized_wave_zero (N : ℕ) (v w : Cutoff N)
    {a b : ℝ} (ha : 3≤a) (hab : a≤b)
    (hv : ∀ Z : ℍ, a<height Z → upperFunction v.value Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N, height Z<b → upperFunction w.value Z=0)
    (t : ℝ) (ht : |t|<Real.log (b/a)) (f : AutomorphicSpace N) :
    multiplier N w (Wave.shiftedQuotientWave N t
      (quotientLocalization N v.value v.smooth f)).val=0 := by
  have hR : 0≤b+1 := by linarith
  refine localized_wave_zero N (logarithmicCuspCutoff N (b+1) hR) v w
    (truncatedLog (b+1) a) (truncatedLog (b+1) b) ?_ ?_ t ?_ f
  · intro Z hZ
    rw [logarithmicCuspCutoff_upper] at hZ
    apply hv Z
    by_contra hn
    exact (not_lt_of_ge (truncatedLog_monotone (b+1) (le_of_not_gt hn))) hZ
  · filter_upwards [hw] with Z hZ
    rw [logarithmicCuspCutoff_upper]
    intro hh
    apply hZ
    by_contra hn
    exact (not_lt_of_ge (truncatedLog_monotone (b+1) (le_of_not_gt hn))) hh
  · change truncatedLog (b+1) a+|(1:ℝ)| * |t|<truncatedLog (b+1) b
    have he := truncatedLog_sub_eq_log (b+1) ha hab (show b≤b+1-1 by linarith)
    norm_num only [abs_one,one_mul]
    linarith

/-- Compact-time wave packets obey the same logarithmic height separation,
with no assumed geometric separator or finite propagation theorem. -/
theorem height_localized_packet_zero (N : ℕ) (v w : Cutoff N)
    {a b : ℝ} (ha : 3≤a) (hab : a≤b)
    (hv : ∀ Z : ℍ, a<height Z → upperFunction v.value Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N, height Z<b → upperFunction w.value Z=0)
    {φ : ℝ → ℂ} (hφ : Wave.ShiftedWaveWeight φ)
    {T : ℝ} (hs : Function.support φ⊆Icc (-T) T)
    (ht : T<Real.log (b/a)) (f : AutomorphicSpace N) :
    multiplier N w (Wave.shiftedQuotientWavePacket N φ hφ
      (quotientLocalization N v.value v.smooth f)).val=0 := by
  have hR : 0≤b+1 := by linarith
  refine localized_packet_zero N (logarithmicCuspCutoff N (b+1) hR) v w
    (truncatedLog (b+1) a) (truncatedLog (b+1) b) ?_ ?_ hφ hs ?_ f
  · intro Z hZ
    rw [logarithmicCuspCutoff_upper] at hZ
    apply hv Z
    by_contra hn
    exact (not_lt_of_ge (truncatedLog_monotone (b+1) (le_of_not_gt hn))) hZ
  · filter_upwards [hw] with Z hZ
    rw [logarithmicCuspCutoff_upper]
    intro hh
    apply hZ
    by_contra hn
    exact (not_lt_of_ge (truncatedLog_monotone (b+1) (le_of_not_gt hn))) hh
  · change truncatedLog (b+1) a+|(1:ℝ)| * T<truncatedLog (b+1) b
    have he := truncatedLog_sub_eq_log (b+1) ha hab (show b≤b+1-1 by linarith)
    norm_num only [abs_one,one_mul]
    linarith

#print axioms height_localized_wave_zero
#print axioms height_localized_packet_zero
end QuantitativeArithmeticMaassModularHeight
