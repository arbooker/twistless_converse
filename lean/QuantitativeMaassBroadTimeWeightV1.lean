module

public import QuantitativeMaassBroadTimeBaseV1
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def broadTimeDensity (L s : ℝ) : ℝ := L*broadTimeBase (L*s)

theorem broadTimeDensity_smooth (L : ℝ) : ContDiff ℝ ∞ (broadTimeDensity L) :=
  contDiff_const.mul (broadTimeBase_smooth.comp (contDiff_const.mul contDiff_id))

theorem broadTimeDensity_support (L : ℝ) (hL : 0 < L) :
    Function.support (broadTimeDensity L) ⊆ Icc (-(1/L)) (1/L) := by
  intro s hs
  have hh : broadTimeBase (L*s) ≠ 0 := by
    intro hz
    exact hs (by simp only [broadTimeDensity,hz,mul_zero])
  have hb := broadTimeBase_support hh
  constructor
  · rw [← neg_div,div_le_iff₀ hL]
    simpa only [mul_comm s L] using hb.1
  · apply (le_div_iff₀ hL).mpr
    simpa only [mul_comm s L] using hb.2

theorem broadTimeDensity_compact (L : ℝ) (hL : 0 < L) : HasCompactSupport (broadTimeDensity L) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (broadTimeDensity_support L hL) isClosed_Icc)

theorem broadTimeDensity_nonneg (L : ℝ) (hL : 0 < L) (s : ℝ) :
    0 ≤ broadTimeDensity L s := mul_nonneg hL.le (broadTimeBase_nonneg _)

theorem broadTimeDensity_mass (L : ℝ) (hL : 0 < L) :
    (∫ s : ℝ, broadTimeDensity L s)=1 := by
  unfold broadTimeDensity
  rw [integral_const_mul,Measure.integral_comp_mul_left,broadTimeBase_mass,
    smul_eq_mul,mul_one,abs_of_pos (inv_pos.mpr hL),mul_inv_cancel₀ hL.ne']

theorem broadTimeDensity_cosine_nonneg (L : ℝ) (hL : 0 < L) (r : ℝ) :
    0 ≤ ∫ s : ℝ, broadTimeDensity L s*Real.cos (r*s) := by
  have he : (fun s => broadTimeDensity L s*Real.cos (r*s)) =
      fun s => L*(broadTimeBase (L*s)*Real.cos ((r/L)*(L*s))) := by
    funext s
    have hh : (r/L)*(L*s)=r*s := by field_simp
    rw [hh]
    unfold broadTimeDensity
    ring
  rw [he,integral_const_mul,Measure.integral_comp_mul_left
    (fun s => broadTimeBase s*Real.cos ((r/L)*s)) L,
    smul_eq_mul,abs_of_pos (inv_pos.mpr hL),← mul_assoc,mul_inv_cancel₀ hL.ne',one_mul]
  exact broadTimeBase_cosine_nonneg (r/L)

theorem broadTimeDensity_cosineSquareMass_half (L : ℝ) (hL : 0 < L) (t : ℝ) :
    1/2 ≤ cosineSquareMass (broadTimeDensity L) t := by
  apply cosineSquareMass_half_le (broadTimeDensity L) (broadTimeDensity_smooth L).continuous
    (broadTimeDensity_compact L hL) (broadTimeDensity_mass L hL) t
  simpa only [mul_assoc] using broadTimeDensity_cosine_nonneg L hL (2*t)

/-- The actual smooth broad packet weight. Its time support is 1/L;
the central frequency t does not enter its L1 mass bound. -/
def broadTimeWeight (L t : ℝ) : ℝ → ℂ := normalizedCosineWeight (broadTimeDensity L) t

theorem broadTimeWeight_smooth (L t : ℝ) : ContDiff ℝ ∞ (broadTimeWeight L t) := by
  unfold broadTimeWeight normalizedCosineWeight
  apply Complex.ofRealCLM.contDiff.comp
  exact ((broadTimeDensity_smooth L).mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const _

theorem broadTimeWeight_compact (L : ℝ) (hL : 0 < L) (t : ℝ) :
    HasCompactSupport (broadTimeWeight L t) :=
  normalizedCosineWeight_compact _ (broadTimeDensity_compact L hL) t

theorem broadTimeWeight_support (L : ℝ) (hL : 0 < L) (t : ℝ) :
    Function.support (broadTimeWeight L t) ⊆ Icc (-(1/L)) (1/L) :=
  (normalizedCosineWeight_support _ t).trans (broadTimeDensity_support L hL)

theorem broadTimeWeight_normalization (L : ℝ) (hL : 0 < L) (t : ℝ) :
    (∫ s : ℝ, broadTimeWeight L t s*(Real.cos (t*s):ℂ))=1 :=
  normalizedCosineWeight_normalization _ t
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (broadTimeDensity_cosineSquareMass_half L hL t))

theorem broadTimeWeight_norm_integral_le (L : ℝ) (hL : 0 < L) (t : ℝ) :
    (∫ s : ℝ, ‖broadTimeWeight L t s‖) ≤ 2 :=
  normalizedCosineWeight_norm_integral_le _ (broadTimeDensity_smooth L).continuous
    (broadTimeDensity_compact L hL) (broadTimeDensity_nonneg L hL)
    (broadTimeDensity_mass L hL) t (broadTimeDensity_cosineSquareMass_half L hL t)

#print axioms broadTimeDensity_mass
#print axioms broadTimeDensity_cosine_nonneg
#print axioms broadTimeWeight_smooth
#print axioms broadTimeWeight_support
#print axioms broadTimeWeight_normalization
#print axioms broadTimeWeight_norm_integral_le

end QuantitativeMaass
