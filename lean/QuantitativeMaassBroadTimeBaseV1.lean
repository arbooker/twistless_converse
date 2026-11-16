module

public import QuantitativeMaassPositiveTimeSquareV1
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap ContDiff

namespace QuantitativeMaass

def broadTimeBump : ContDiffBump (0:ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def broadTimeSeed : SchwartzMap ℝ ℂ :=
  ((broadTimeBump.hasCompactSupport_normed (μ := volume)).comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp broadTimeBump.contDiff_normed)

theorem broadTimeSeed_real (s : ℝ) : ((broadTimeSeed s).re:ℂ)=broadTimeSeed s := rfl

theorem broadTimeSeed_nonneg (s : ℝ) : 0 ≤ (broadTimeSeed s).re :=
  broadTimeBump.nonneg_normed s

theorem broadTimeSeed_even : Function.Even broadTimeSeed := by
  intro s
  change (broadTimeBump.normed volume (-s):ℂ)=(broadTimeBump.normed volume s:ℂ)
  rw [broadTimeBump.normed_neg]

theorem broadTimeSeed_compact : HasCompactSupport (broadTimeSeed : ℝ → ℂ) :=
  (broadTimeBump.hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero

theorem broadTimeSeed_mass : (∫ s : ℝ, broadTimeSeed s)=1 := by
  change (∫ s : ℝ, (broadTimeBump.normed volume s:ℂ))=1
  rw [integral_complex_ofReal,broadTimeBump.integral_normed,Complex.ofReal_one]

theorem broadTimeSeed_support : Function.support broadTimeSeed ⊆ Icc (-(1/2:ℝ)) (1/2) := by
  intro s hs
  have hh : s ∈ Function.support (broadTimeBump.normed volume) := by
    change broadTimeBump.normed volume s ≠ 0
    change (broadTimeBump.normed volume s:ℂ) ≠ 0 at hs
    exact_mod_cast hs
  rw [broadTimeBump.support_normed_eq] at hh
  change dist s 0 < (1/2:ℝ) at hh
  rw [dist_zero_right,Real.norm_eq_abs] at hh
  exact abs_le.mp hh.le

/-- A fixed smooth even probability density with nonnegative cosine
transform and time support in [-1,1], constructed from an actual bump. -/
def broadTimeBase : ℝ → ℝ := positiveTimeSquare broadTimeSeed

theorem broadTimeBase_smooth : ContDiff ℝ ∞ broadTimeBase :=
  Complex.reCLM.contDiff.comp ((timeConvolution broadTimeSeed broadTimeSeed).smooth ⊤)

theorem broadTimeBase_compact : HasCompactSupport broadTimeBase :=
  positiveTimeSquare_compact broadTimeSeed broadTimeSeed_compact

theorem broadTimeBase_nonneg (s : ℝ) : 0 ≤ broadTimeBase s :=
  positiveTimeSquare_nonneg broadTimeSeed broadTimeSeed_real broadTimeSeed_nonneg s

theorem broadTimeBase_mass : (∫ s : ℝ, broadTimeBase s)=1 :=
  positiveTimeSquare_mass broadTimeSeed broadTimeSeed_real broadTimeSeed_even broadTimeSeed_mass

theorem broadTimeBase_cosine_nonneg (r : ℝ) :
    0 ≤ ∫ s : ℝ, broadTimeBase s*Real.cos (r*s) :=
  positiveTimeSquare_cosine_nonneg broadTimeSeed broadTimeSeed_real broadTimeSeed_even r

theorem broadTimeBase_support : Function.support broadTimeBase ⊆ Icc (-1:ℝ) 1 := by
  intro s hs
  have hh : s ∈ Function.support (timeConvolution broadTimeSeed broadTimeSeed) := by
    intro hz
    exact hs (by simp only [broadTimeBase,positiveTimeSquare,hz,Complex.zero_re])
  have hb := timeConvolution_support broadTimeSeed broadTimeSeed (1/2) (1/2)
    broadTimeSeed_support broadTimeSeed_support hh
  norm_num at hb
  exact hb

#print axioms broadTimeSeed_mass
#print axioms broadTimeBase_smooth
#print axioms broadTimeBase_nonneg
#print axioms broadTimeBase_mass
#print axioms broadTimeBase_cosine_nonneg
#print axioms broadTimeBase_support

end QuantitativeMaass
