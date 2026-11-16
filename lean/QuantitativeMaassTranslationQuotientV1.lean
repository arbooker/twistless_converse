module

public import AsymptoticClassicalPeterssonMeasureV1
public import AsymptoticRamifiedNonzeroSumV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticCongruenceWeight AsymptoticClassicalPetersson AsymptoticIntegralSubgroup
open AsymptoticCompactBranch AsymptoticMassTransport

namespace QuantitativeMaass

/-- Level zero is the actual integral translation group in the existing
projective quotient construction. No finite-index assertion is involved. -/
theorem gamma_zero_translation (g : gamma 0) : ∃ n : ℤ,g.val=translationLabel (n:ℚ) := by
  have hc : representative g 1 0=0 := by
    have hm := CongruenceSubgroup.Gamma0_mem.mp (representative_mem g)
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_zero,zero_dvd_iff] using hm
  obtain ⟨n,hn⟩ := triangular_label (representative g) hc
  exact ⟨n,(representative_label g).symm.trans hn⟩

theorem gamma_zero_strip_unique (z : ℍ) (hz : z∈strip) (g : gamma 0)
    (hg : g.val • z∈strip) : g=1 := by
  obtain ⟨n,hn⟩ := gamma_zero_translation g
  have hzero := translation_eq_zero hg hz n (by rw [hn])
  apply Subtype.ext
  simpa only [hzero,Int.cast_zero,OneMemClass.coe_one,AsymptoticRamifiedTwistedLaw.translationLabel_zero] using hn

theorem translation_quotient_weight (ε : ℝ) (t : ℕ) (z : ℍ) (hz : z∈strip) :
    weight 0 ε t z=cap ε t z^2 := by
  classical
  unfold weight
  rw [tsum_eq_single (1 : gamma 0)]
  · simp only [OneMemClass.coe_one,one_smul,Set.indicator_of_mem hz]
  · intro g hg
    apply Set.indicator_of_notMem
    exact fun h => hg (gamma_zero_strip_unique z hz g h)

/-- The orbit density for the translation quotient is precisely the unit
strip indicator, so its measure is the genuine cylinder measure. -/
theorem translation_quotient_density : density 0=strip.indicator (fun _ => (1:ℝ≥0∞)) := by
  funext z
  classical
  by_cases hz : z∈strip
  · rw [density,amplitude,Set.indicator_of_mem hz,Set.indicator_of_mem hz,
      translation_quotient_weight 1 1 z hz,
      Real.sqrt_sq (cap_pos (by norm_num : (0:ℝ)<1) 1 z).le,
      div_self (cap_pos (by norm_num : (0:ℝ)<1) 1 z).ne']
    norm_num
  · rw [density,amplitude,Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
    simp only [norm_zero,zero_pow (by decide : 2≠0),ENNReal.ofReal_zero]

theorem translation_quotient_measure : quotientMeasure 0=volume.restrict strip := by
  rw [quotientMeasure,translation_quotient_density]
  exact withDensity_indicator_one strip_measurable

/-- Every level, including the infinite-volume translation quotient, has
a sigma-finite actual quotient measure. -/
instance quotientMeasure_sigmaFinite_all (N : ℕ) : SigmaFinite (quotientMeasure N) := by
  unfold quotientMeasure density
  infer_instance

#print axioms gamma_zero_translation
#print axioms gamma_zero_strip_unique
#print axioms translation_quotient_weight
#print axioms translation_quotient_density
#print axioms translation_quotient_measure

end QuantitativeMaass
