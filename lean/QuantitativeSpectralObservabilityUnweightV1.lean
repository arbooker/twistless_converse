module

public import QuantitativeSpectralObservabilityCoverV1
public import QuantitativeSpectralCoverUnweightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservabilityUnweight

open Matrix UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticCompactBranch
open QuantitativeHolomorphic QuantitativeSpectralModularHeight
open QuantitativeSpectralObservability QuantitativeSpectralCoverUnweight
open scoped MatrixGroups ENNReal lp

theorem wide_modular_height_lower (g : SL(2,ℤ)) {B a H : ℝ}
    (hB : 0 ≤ B) (hg : MatrixEntryBound g.val B) (z : ℍ)
    (hre : |z.re| ≤ 2) (hlo : a ≤ z.im) (hhi : z.im ≤ H) :
    a/(B^2*(H+3)^2) ≤ (g • z).im := by
  have hz : ‖(z:ℂ)‖ ≤ H+2 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z:ℂ)
    change ‖(z:ℂ)‖ ≤ |z.re|+|z.im| at hh
    rw [abs_of_pos z.im_pos] at hh
    linarith
  have hd : ‖denom g z‖ ≤ B*(H+3) := by
    simpa only [ModularGroup.denom_apply,add_assoc,show (2:ℝ)+1=3 by norm_num]
      using matrix_denominator_bound hB hg (z:ℂ) hz
  have hpos : 0<‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero_of_im g z.im_ne_zero)
  have hbpos : 0<B*(H+3) := hpos.trans_le hd
  have hsq : Complex.normSq (denom g z) ≤ B^2*(H+3)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) hbpos.le).mpr hd
  rw [ModularGroup.im_smul_eq_div_normSq]
  exact (div_le_div_of_nonneg_right hlo (by positivity)).trans
    (div_le_div_of_nonneg_left z.im_pos.le (normSq_denom_pos g z.im_ne_zero) hsq)

/-- Explicit lower height for the matching overlapping compact cutoff. -/
theorem wideCompactCover_height_lower (N : ℕ) (hN : 0<N) (H : ℝ)
    {z : ℍ} (hz : z∈wideCompactCover N H) :
    ((1:ℝ)/4)/((coverBound N hN)^2*(H+3)^2) ≤ z.im := by
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  dsimp only at *
  rw [←map_inv,integralLabel_action]
  exact wide_modular_height_lower q.out⁻¹ (by linarith [coverBound_one_le N hN])
    (coverBound_entry N hN q) w (abs_le.mpr ⟨by linarith [hw.1],hw.2.1⟩)
    hw.2.2.1 hw.2.2.2

theorem wideCompactCover_cap_inverse (N : ℕ) (hN : 0<N) (H : ℝ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) {z : ℍ} (hz : z∈wideCompactCover N H) :
    (cap ε t z)⁻¹ ≤ (max 1 (4*ε*(coverBound N hN)^2*(H+3)^2))^t := by
  have hH : 0<H+3 := by
    obtain ⟨q,w,hw,he⟩ := mem_iUnion.mp hz
    linarith [hw.2.2.1,hw.2.2.2]
  have hB : 0<coverBound N hN := lt_of_lt_of_le zero_lt_one (coverBound_one_le N hN)
  have hl := wideCompactCover_height_lower N hN H hz
  have hh := cap_inverse_of_height hε (show 0<((1:ℝ)/4)/((coverBound N hN)^2*(H+3)^2) by positivity) t z hl
  convert hh using 1
  congr 2
  field_simp

/-- The concrete unweighting coefficient, with a genuine compact cutoff. -/
def coefficient (N : ℕ) (H ε : ℝ) (t : ℕ) : ℍ → ℂ :=
  (wideCompactCover N H).indicator (fun z => Complex.ofReal ((cap ε t z)⁻¹))

theorem coefficient_measurable (N : ℕ) (hN : 0 < N) (H ε : ℝ) (t : ℕ) :
    Measurable (coefficient N H ε t) :=
  (Complex.measurable_ofReal.comp (cap_continuous ε t).measurable.inv).indicator
    (wideCompactCover_compact N hN H).measurableSet

theorem coefficient_norm_le (N : ℕ) (hN : 0 < N) (H : ℝ) {ε : ℝ}
    (hε : 0 < ε) (t : ℕ) (z : ℍ) :
    ‖coefficient N H ε t z‖ ≤ (max 1 (4*ε*(coverBound N hN)^2*(H+3)^2))^t := by
  classical
  by_cases hz : z ∈ wideCompactCover N H
  · rw [coefficient, Set.indicator_of_mem hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (cap_pos hε t z))]
    exact wideCompactCover_cap_inverse N hN H hε t hz
  · rw [coefficient, Set.indicator_of_notMem hz, norm_zero]
    positivity

#print axioms wideCompactCover_height_lower
#print axioms wideCompactCover_cap_inverse
#print axioms coefficient_norm_le

end QuantitativeSpectralObservabilityUnweight
