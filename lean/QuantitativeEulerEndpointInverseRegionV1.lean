module

public import QuantitativeEulerEndpointInverseV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode AsymptoticIntegralSubgroup
open scoped Classical

theorem rational_translation_re (r : ℚ) (z : ℍ) :
    (translationLabel r • z).re=z.re+(r : ℝ) := by
  rw [AsymptoticCompactTranslation.label_action]
  simpa only [Complex.add_re,Complex.ofReal_re,UpperHalfPlane.coe_re] using
    congrArg Complex.re (AsymptoticMobiusFold.translation_action (r : ℝ) z)

/-- Although the inverse uses q translated images, all of them fit in the
same fixed-width strip. Both imaginary-height cutoffs are unchanged. -/
theorem inverseRegion_strip (q : ℕ) {s : Set ℍ} {L H : ℝ}
    (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, L≤z.im) (hhi : ∀ z∈s, z.im≤H) :
    ∀ z∈inverseRegion q s, -1≤z.re ∧ z.re≤2 ∧ L≤z.im ∧ z.im≤H := by
  intro z hz
  rcases hz with hz | hz
  · have hr := abs_le.mp (hre z hz)
    exact ⟨hr.1,hr.2.trans (by norm_num),hlo z hz,hhi z hz⟩
  · rcases Set.mem_iUnion.mp hz with ⟨j,hj⟩
    rcases hj with ⟨y,hy,rfl⟩
    rw [symbolBranch_label,rational_translation_re,AsymptoticCompactTranslation.label_im]
    have hq : 0<(q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
    have hr0 : 0≤(j.val : ℝ)/q := div_nonneg (Nat.cast_nonneg _) hq.le
    have hr1 : (j.val : ℝ)/q≤1 := (div_le_one hq).2 (by exact_mod_cast j.isLt.le)
    have hry := abs_le.mp (hre y hy)
    push_cast
    exact ⟨by linarith,by linarith,hlo y hy,hhi y hy⟩

#print axioms rational_translation_re
#print axioms inverseRegion_strip
end QuantitativeEulerEndpointPrepared
