module

public import QuantitativeMaassHalfDensityTestV1
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass

/-- Uniform quadratic Taylor remainder from a Lipschitz derivative. -/
theorem norm_taylor_remainder_le (g g' : ℝ → ℂ) (K : ℝ≥0)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hK : LipschitzWith K g') (a b : ℝ) :
    ‖g b-g a-(b-a) • g' a‖≤(K:ℝ)*‖b-a‖^2 := by
  have hd (x : ℝ) : HasDerivAt (fun x => g x-(x-a) • g' a) (g' x-g' a) x := by
    simpa only [one_smul,id_eq] using
      (hg x).fun_sub (((hasDerivAt_id x).sub_const a).smul_const (g' a))
  have hb (x : ℝ) (hx : x∈segment ℝ a b) : ‖g' x-g' a‖≤(K:ℝ)*‖b-a‖ := by
    exact (hK.norm_sub_le x a).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) K.coe_nonneg)
  have hm := (convex_segment a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) hb (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [sub_self,zero_smul,sub_zero,sub_right_comm,pow_two,mul_assoc] using hm

/-- The translated test as an actual local Lebesgue L2 vector. -/
def translatedLogTest (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) (x : ℝ) :
    Lp ℂ 2 (volume.restrict (Icc A B)) :=
  logTestVector A B (fun y => g (y-x)) (hg.comp (continuous_id.sub continuous_const))

theorem translatedLogTest_ae (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) (x : ℝ) :
    (translatedLogTest A B g hg x : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)] fun y => g (y-x) :=
  logTestVector_ae A B _ _

/-- The scalar remainder bound controls the actual L2 Taylor remainder
uniformly in the spatial test variable on a compact band. -/
theorem translatedLogTest_remainder_le (A B : ℝ) (g g' : ℝ → ℂ)
    (hg : Continuous g) (hg' : Continuous g') (K : ℝ≥0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hK : LipschitzWith K g') (x z : ℝ) :
    ‖translatedLogTest A B g hg z-translatedLogTest A B g hg x-
      (z-x) • (-translatedLogTest A B g' hg' x)‖≤
      (measureUnivNNReal (volume.restrict (Icc A B)):ℝ)^((2:ENNReal).toReal⁻¹)*
        ((K:ℝ)*‖z-x‖^2) := by
  apply Lp.norm_le_of_ae_bound (mul_nonneg K.coe_nonneg (sq_nonneg _))
  filter_upwards [Lp.coeFn_sub
    (translatedLogTest A B g hg z-translatedLogTest A B g hg x)
    ((z-x) • (-translatedLogTest A B g' hg' x)),
    Lp.coeFn_sub (translatedLogTest A B g hg z) (translatedLogTest A B g hg x),
    Lp.coeFn_smul (z-x) (-translatedLogTest A B g' hg' x),
    Lp.coeFn_neg (translatedLogTest A B g' hg' x),
    translatedLogTest_ae A B g hg z,translatedLogTest_ae A B g hg x,
    translatedLogTest_ae A B g' hg' x] with y hsub hsub' hsmul hneg hz hx hd'
  simp only [hsub,Pi.sub_apply,hsub',hsmul,Pi.smul_apply,hneg,Pi.neg_apply,hz,hx,hd']
  have he : (y-z)-(y-x)=-(z-x) := by ring
  have h := norm_taylor_remainder_le g g' K hd hK (y-x) (y-z)
  simpa only [he,neg_smul,smul_neg,norm_neg] using h

#print axioms norm_taylor_remainder_le
#print axioms translatedLogTest_remainder_le

end QuantitativeMaass
